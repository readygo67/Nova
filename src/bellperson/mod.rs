//! Support for generating R1CS from [Bellperson].
//!
//! [Bellperson]: https://github.com/filecoin-project/bellperson

pub mod r1cs;
pub mod shape_cs;
pub mod solver;

#[cfg(test)]
mod tests {
  use crate::{
    bellperson::{
      r1cs::{NovaShape, NovaWitness},
      shape_cs::ShapeCS,
      solver::SatisfyingAssignment,
    },
    traits::Group,
  };
  use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
  use ff::PrimeField;

  fn synthesize_alloc_bit<Fr: PrimeField, CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
  ) -> Result<(), SynthesisError> {
    // get two bits as input and check that they are indeed bits
    // AllocatedNum::alloc 有两个输入参数，第一个参数为cs ， 第二个参数为value 
    let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::ONE))?;
    let _ = a.inputize(cs.namespace(|| "a is input"));

    // A * B = C，  (1-x) * x = 0
    cs.enforce(
      || "check a is 0 or 1",
      |lc| lc + CS::one() - a.get_variable(),
      |lc| lc + a.get_variable(),
      |lc| lc,
    );

    /*
    为变量 b 创建一个 AllocatedNum 对象，并将其初始化为值 0。AllocatedNum 是约束系统中的一种类型，表示一个分配的数值。它将被分配到有限域 Fr 中的某个元素上。 在这里，我们使用 alloc 方法来创建一个表示变量 b 的 AllocatedNum 对象，并将其初始化为 0。在创建时，需要提供一些参数，如约束系统的命名空间和一个闭包，该闭包返回 Ok(Fr::ZERO)，表示我们将变量 b 分配到有限域 Fr 上的 0 元素。
    注意该行代码结尾的 ?，它可以将任何 Result 类型转换为 Option 类型。如果初始化出现错误，则 ? 会将错误转换为 None。在这里，如果创建 AllocatedNum 对象或者分配出现错误，代码将立即从该函数返回。
     */
    
    let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::ZERO))?;
    // 该代码是为了将变量 b 标记为约束系统的公共输入。类似于把变量 b 标记为 "公开的"，它将被约束系统暴露并作为输入提供给 ZKP 协议的验证者。这里使用的 _ 变量名是为了避免再次使用变量 b，因为 inputize 方法不返回任何值，我们也不会在后续代码中使用变量 _。
    let _ = b.inputize(cs.namespace(|| "b is input"));
    cs.enforce(
      || "check b is 0 or 1",
      |lc| lc + CS::one() - b.get_variable(),
      |lc| lc + b.get_variable(),
      |lc| lc,
    );
    Ok(())
  }

  fn test_alloc_bit_with<G>()
  where
    G: Group,
  {
    // First create the shape
    let mut cs: ShapeCS<G> = ShapeCS::new();
    let _ = synthesize_alloc_bit(&mut cs);
    let (shape, ck) = cs.r1cs_shape();

    // Now get the assignment
    let mut cs: SatisfyingAssignment<G> = SatisfyingAssignment::new();
    let _ = synthesize_alloc_bit(&mut cs);
    let (inst, witness) = cs.r1cs_instance_and_witness(&shape, &ck).unwrap();

    // Make sure that this is satisfiable
    assert!(shape.is_sat(&ck, &inst, &witness).is_ok());
  }

  #[test]
  fn test_alloc_bit() {
    type G = pasta_curves::pallas::Point;
    test_alloc_bit_with::<G>();
  }
}
