//! Support for generating R1CS shape using bellperson.

use std::{
  cmp::Ordering,
  collections::{BTreeMap, HashMap},
};

use crate::traits::Group;
use bellperson::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use core::fmt::Write;
use ff::{Field, PrimeField};

#[derive(Clone, Copy)]
struct OrderedVariable(Variable);

#[derive(Debug)]
// 定义一个enum
enum NamedObject {
  Constraint(usize),
  Var(Variable),
  Namespace,
}

impl Eq for OrderedVariable {}
impl PartialEq for OrderedVariable {
  fn eq(&self, other: &OrderedVariable) -> bool {
    match (self.0.get_unchecked(), other.0.get_unchecked()) {
      (Index::Input(ref a), Index::Input(ref b)) => a == b,
      (Index::Aux(ref a), Index::Aux(ref b)) => a == b,
      _ => false,
    }
  }
}
impl PartialOrd for OrderedVariable {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl Ord for OrderedVariable {
  fn cmp(&self, other: &Self) -> Ordering {
    match (self.0.get_unchecked(), other.0.get_unchecked()) {
      (Index::Input(ref a), Index::Input(ref b)) => a.cmp(b),
      (Index::Aux(ref a), Index::Aux(ref b)) => a.cmp(b),
      (Index::Input(_), Index::Aux(_)) => Ordering::Less,
      (Index::Aux(_), Index::Input(_)) => Ordering::Greater,
    }
  }
}

#[allow(clippy::upper_case_acronyms)]
/// `ShapeCS` is a `ConstraintSystem` for creating `R1CSShape`s for a circuit.
pub struct ShapeCS<G: Group>
where
  G::Scalar: PrimeField + Field,
{
  named_objects: HashMap<String, NamedObject>,  //使用hashMap保存？？
  current_namespace: Vec<String>,  //定义字符串动态数组，
  #[allow(clippy::type_complexity)]
  /// All constraints added to the `ShapeCS`.
  /// tuple 动态数组
  pub constraints: Vec<(
    LinearCombination<G::Scalar>,  //A constraint
    LinearCombination<G::Scalar>,  //B constraint
    LinearCombination<G::Scalar>,  //C con
    String,
  )>,
  inputs: Vec<String>,
  aux: Vec<String>,
}
//该函数首先利用一个 BTreeMap 类型来存储有序变量和对应的系数。在循环遍历线性组合时，对于每个 (var,coeff) 元素，它将该元素的系数加到对应有序变量的系数上，并在需要时将该有序变量添加到 BTreeMap 中。最后，该函数还会移除系数为零的项，以便得到一个标准化的结果。
fn proc_lc<Scalar: PrimeField>(
  terms: &LinearCombination<Scalar>,
) -> BTreeMap<OrderedVariable, Scalar> {
  let mut map = BTreeMap::new();
  /*在这段 Rust 代码中，循环遍历了一个被称为 terms 的 LinearCombination 类型的线性组合。对于每个 (var, coeff) 元素，它执行以下操作：

  利用 var 创建一个 OrderedVariable 实例。
  查询 map 中是否已经存在键为 OrderedVariable(var) 的项。
  如果不存在，则先将键值对 (OrderedVariable(var), Scalar::ZERO) 插入到 map 中。
  将当前系数 coeff 加到对应 OrderedVariable 的值中。
  该循环的最终结果是，我们将所有的项按照 OrderedVariable 的顺序排好了序，并且对于每个变量，我们都计算了对应的系数。也就是说，该循环将一个无序的线性组合转换成了一个有序的系数映射表，方便了后续的处理。 */
  for (var, &coeff) in terms.iter() {
    map
      .entry(OrderedVariable(var))
      .or_insert_with(|| Scalar::ZERO)
      .add_assign(&coeff);
  }

  // Remove terms that have a zero coefficient to normalize
  let mut to_remove = vec![];
  for (var, coeff) in map.iter() {
    if coeff.is_zero().into() {
      to_remove.push(*var)
    }
  }

  for var in to_remove {
    map.remove(&var);
  }

  map
}

//为shapeCS的方法
impl<G: Group> ShapeCS<G>
where
  G::Scalar: PrimeField, 
{
  /// Create a new, default `ShapeCS`,
  pub fn new() -> Self {
    ShapeCS::default()
  }

  /// Returns the number of constraints defined for this `ShapeCS`.
  /// 返回cs的约束个数
  pub fn num_constraints(&self) -> usize {
    self.constraints.len()
  }

  /// Returns the number of inputs defined for this `ShapeCS`.
  /// 返回inputs的个数
  pub fn num_inputs(&self) -> usize {
    self.inputs.len()
  }

  /// Returns the number of aux inputs defined for this `ShapeCS`.
  /// auxInputs 是什么？
  pub fn num_aux(&self) -> usize {
    self.aux.len()
  }

  /// Print all public inputs, aux inputs, and constraint names.
  /// #[allow(dead_code)] 是一个编译器指令，用于告诉 Rust 编译器忽略未使用的变量或函数而不产生未使用的变量或函数的警告
  #[allow(dead_code)]
  pub fn pretty_print_list(&self) -> Vec<String> {
    let mut result = Vec::new();

    for input in &self.inputs {
      result.push(format!("INPUT {input}"));
    }
    for aux in &self.aux {
      result.push(format!("AUX {aux}"));
    }

    for (_a, _b, _c, name) in &self.constraints {
      result.push(name.to_string());
    }

    result
  }

  /// Print all iputs and a detailed representation of each constraint.
  #[allow(dead_code)]
  pub fn pretty_print(&self) -> String {
    let mut s = String::new();

    for input in &self.inputs {
      writeln!(s, "INPUT {}", &input).unwrap()
    }

    let negone = -<G::Scalar>::ONE;

    let powers_of_two = (0..G::Scalar::NUM_BITS)
      .map(|i| G::Scalar::from(2u64).pow_vartime([u64::from(i)]))
      .collect::<Vec<_>>();

    let pp = |s: &mut String, lc: &LinearCombination<G::Scalar>| {
      s.push('(');
      let mut is_first = true;
      for (var, coeff) in proc_lc::<G::Scalar>(lc) {
        if coeff == negone {
          s.push_str(" - ")
        } else if !is_first {
          s.push_str(" + ")
        }
        is_first = false;

        if coeff != <G::Scalar>::ONE && coeff != negone {
          for (i, x) in powers_of_two.iter().enumerate() {
            if x == &coeff {
              write!(s, "2^{i} . ").unwrap();
              break;
            }
          }

          write!(s, "{coeff:?} . ").unwrap()
        }

        match var.0.get_unchecked() {
          Index::Input(i) => {
            write!(s, "`I{}`", &self.inputs[i]).unwrap();
          }
          Index::Aux(i) => {
            write!(s, "`A{}`", &self.aux[i]).unwrap();
          }
        }
      }
      if is_first {
        // Nothing was visited, print 0.
        s.push('0');
      }
      s.push(')');
    };

    for (a, b, c, name) in &self.constraints {
      s.push('\n');

      write!(s, "{name}: ").unwrap();
      pp(&mut s, a);
      write!(s, " * ").unwrap();
      pp(&mut s, b);
      s.push_str(" = ");
      pp(&mut s, c);
    }

    s.push('\n');

    s
  }

  /// Associate `NamedObject` with `path`.
  /// `path` must not already have an associated object.
  /// 在name_object中插入(K,V)
  fn set_named_obj(&mut self, path: String, to: NamedObject) {
    assert!(
      !self.named_objects.contains_key(&path),
      "tried to create object at existing path: {path}"
    );

    self.named_objects.insert(path, to);
  }
}

impl<G: Group> Default for ShapeCS<G>
where
  G::Scalar: PrimeField,
{
  fn default() -> Self {
    let mut map = HashMap::new();
    map.insert("ONE".into(), NamedObject::Var(ShapeCS::<G>::one()));
    ShapeCS {
      named_objects: map,
      current_namespace: vec![],
      constraints: vec![],
      inputs: vec![String::from("ONE")],
      aux: vec![],
    }
  }
}

impl<G: Group> ConstraintSystem<G::Scalar> for ShapeCS<G>
where
  G::Scalar: PrimeField,
{
  type Root = Self;

  //FnOnce 是一个 trait，用来表示能够被调用一次的闭包（或函数）。它的作用是允许您传递任意可调用的类型作为参数，并在需要时调用它们。
  // alloc 方法用于分配一个新的变量，并将其添加到约束系统中 如果分配成功，返回一个该变量在aux动态数组的索引作为 ID,，否则返回一个错误
  // A 是一个函数，将A 类型转成AR？
  fn alloc<F, A, AR>(&mut self, annotation: A, _f: F) -> Result<Variable, SynthesisError>
  where
    F: FnOnce() -> Result<G::Scalar, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    let path = compute_path(&self.current_namespace, &annotation().into());
    self.aux.push(path);

    Ok(Variable::new_unchecked(Index::Aux(self.aux.len() - 1)))
  }

// alloc 方法用于分配一个新的变量，并将其添加到约束系统中 如果分配成功，返回一个该变量在inputs动态数组的索引作为ID,，否则返回一个错误
  fn alloc_input<F, A, AR>(&mut self, annotation: A, _f: F) -> Result<Variable, SynthesisError>
  where
    F: FnOnce() -> Result<G::Scalar, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    let path = compute_path(&self.current_namespace, &annotation().into());
    self.inputs.push(path);

    Ok(Variable::new_unchecked(Index::Input(self.inputs.len() - 1)))
  }

  // 添加A,B,C 约束
  fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
  where
    A: FnOnce() -> AR,
    AR: Into<String>,
    LA: FnOnce(LinearCombination<G::Scalar>) -> LinearCombination<G::Scalar>,
    LB: FnOnce(LinearCombination<G::Scalar>) -> LinearCombination<G::Scalar>,
    LC: FnOnce(LinearCombination<G::Scalar>) -> LinearCombination<G::Scalar>,
  {
    let path = compute_path(&self.current_namespace, &annotation().into()); //build path
    let index = self.constraints.len();  //获得约束的index
    self.set_named_obj(path.clone(), NamedObject::Constraint(index)); //将path 和对应的nameObject存储

    let a = a(LinearCombination::zero()); //看起来并没有实际约束
    let b = b(LinearCombination::zero());
    let c = c(LinearCombination::zero());

    self.constraints.push((a, b, c, path));
  }

  //增加一个nameSpace
  fn push_namespace<NR, N>(&mut self, name_fn: N)
  where
    NR: Into<String>,
    N: FnOnce() -> NR,
  {
    let name = name_fn().into();
    let path = compute_path(&self.current_namespace, &name);
    self.set_named_obj(path, NamedObject::Namespace);
    self.current_namespace.push(name);
  }

  fn pop_namespace(&mut self) {
    assert!(self.current_namespace.pop().is_some());
  }

  fn get_root(&mut self) -> &mut Self::Root {
    self
  }
}

//计算给定字符串数组 ns 和当前字符串 this 的路径。它将数组中的所有字符串连接起来，以 / 作为分隔符，并在末尾添加当前字符串，以获得完整的路径字符串。例如，当输入为 ["a", "b", "c"] 和 "d" 时，函数将返回字符串 "a/b/c/d"
fn compute_path(ns: &[String], this: &str) -> String {
  assert!(
    !this.chars().any(|a| a == '/'), //如果a中有"/"字符，报错
    "'/' is not allowed in names"
  );

  let mut name = ns.join("/");
  if !name.is_empty() {
    name.push('/');
  }

  name.push_str(this);

  name
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_compute_path() {
    let ns = vec!["path".to_string(), "to".to_string(), "dir".to_string()];
    let this = "file";
    assert_eq!(compute_path(&ns, this), "path/to/dir/file");

    let ns = vec!["".to_string(), "".to_string(), "".to_string()];
    let this = "file";
    assert_eq!(compute_path(&ns, this), "///file");

    let ns = vec![];
    let this = "file";
    assert_eq!(compute_path(&ns, this), "file");
  }

  #[test]
  #[should_panic(expected = "'/' is not allowed in names")]
  fn test_compute_path_invalid() {
    let ns = vec!["path".to_string(), "to".to_string(), "dir".to_string()];
    let this = "fi/le";
    compute_path(&ns, this);
  }
}
