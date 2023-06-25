//! This module provides an implementation of a commitment engine
use crate::{
  errors::NovaError,
  traits::{
    commitment::{CommitmentEngineTrait, CommitmentTrait},
    AbsorbInROTrait, CompressedGroup, Group, ROTrait, TranscriptReprTrait,
  },
};
use core::{
  fmt::Debug,
  marker::PhantomData,
  ops::{Add, AddAssign, Mul, MulAssign},
};
use ff::Field;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// A type that holds commitment generators
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
// pederson commitment key
pub struct CommitmentKey<G: Group> {
  ck: Vec<G::PreprocessedGroupElement>,
  _p: PhantomData<G>,
}

/// A type that holds a commitment
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct Commitment<G: Group> {
  pub(crate) comm: G,
}

/// A type that holds a compressed commitment
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CompressedCommitment<G: Group> {
  comm: G::CompressedGroupElement,
}

impl<G: Group> CommitmentTrait<G> for Commitment<G> {
  type CompressedCommitment = CompressedCommitment<G>;

  fn compress(&self) -> Self::CompressedCommitment {
    CompressedCommitment {
      comm: self.comm.compress(),
    }
  }

  fn to_coordinates(&self) -> (G::Base, G::Base, bool) {
    self.comm.to_coordinates()
  }

  fn decompress(c: &Self::CompressedCommitment) -> Result<Self, NovaError> {
    let comm = c.comm.decompress();
    if comm.is_none() {
      return Err(NovaError::DecompressionError);
    }
    Ok(Commitment {
      comm: comm.unwrap(),
    })
  }
}

impl<G: Group> Default for Commitment<G> {
  fn default() -> Self {
    Commitment { comm: G::zero() }
  }
}

impl<G: Group> TranscriptReprTrait<G> for Commitment<G> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    let (x, y, is_infinity) = self.comm.to_coordinates();
    let is_infinity_byte = (!is_infinity).into();
    [
      x.to_transcript_bytes(),
      y.to_transcript_bytes(),
      [is_infinity_byte].to_vec(),
    ]
    .concat()
  }
}

impl<G: Group> AbsorbInROTrait<G> for Commitment<G> {
  fn absorb_in_ro(&self, ro: &mut G::RO) {
    let (x, y, is_infinity) = self.comm.to_coordinates();
    ro.absorb(x);
    ro.absorb(y);
    ro.absorb(if is_infinity {
      G::Base::ONE
    } else {
      G::Base::ZERO
    });
  }
}

impl<G: Group> TranscriptReprTrait<G> for CompressedCommitment<G> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    self.comm.to_transcript_bytes()
  }
}

impl<G: Group> MulAssign<G::Scalar> for Commitment<G> {
  fn mul_assign(&mut self, scalar: G::Scalar) {
    let result = (self as &Commitment<G>).comm * scalar;
    *self = Commitment { comm: result };
  }
}

/*
'a 和 'b 是Rust中的生命周期变量，用于表示引用的有效范围。具体来说，'a 和'b 表示 self 和 scalar 的有效范围，即它们分别引用的值在函数执行期间必须保持有效。
'a 和 'b 加上前缀 ' 表示这是生命周期变量。在Rust中，生命周期是指引用的有效期，确保了引用的合法性和有效性。我们需要使用生命周期变量来避免产生悬垂引用，确保引用所指向的值在程序中一直保持有效，从而避免了许多内存问题。
在这个实现中，'a 和 'b 是用于支持在引用上使用生命周期注释的方式。由于Commitment和G::Scalar是不同的类型，因此必须将其作为引用来使用。'a 和 'b 实际上就是声明了 &'a Commitment<G> 和 &'b G::Scalar 这两种不同的引用类型，告诉编译器它们的生命周期和有效范围，从而保证代码的正确性。
 */
impl<'a, 'b, G: Group> Mul<&'b G::Scalar> for &'a Commitment<G> {
  type Output = Commitment<G>;
  fn mul(self, scalar: &'b G::Scalar) -> Commitment<G> {
    Commitment {
      comm: self.comm * scalar,
    }
  }
}

/*
第二个函数 Mul<G::Scalar> 是一个针对 G::Scalar 类型值的乘法运算符重载实现，它接受一个 G::Scalar 类型的值，并返回一个 Commitment<G> 类型的值。该函数的目的是将一个 Commitment<G> 类型的值与一个 G::Scalar 类型的值相乘，并返回结果。
 */
impl<G: Group> Mul<G::Scalar> for Commitment<G> {
  type Output = Commitment<G>;

  fn mul(self, scalar: G::Scalar) -> Commitment<G> {
    Commitment {
      comm: self.comm * scalar,
    }
  }
}

// commitment相加
impl<'b, G: Group> AddAssign<&'b Commitment<G>> for Commitment<G> {
  fn add_assign(&mut self, other: &'b Commitment<G>) {
    let result = (self as &Commitment<G>).comm + other.comm;
    *self = Commitment { comm: result };
  }
}

// commitment相加
impl<'a, 'b, G: Group> Add<&'b Commitment<G>> for &'a Commitment<G> {
  type Output = Commitment<G>;
  fn add(self, other: &'b Commitment<G>) -> Commitment<G> {
    Commitment {
      comm: self.comm + other.comm,
    }
  }
}

macro_rules! define_add_variants {
  (G = $g:path, LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
    impl<'b, G: $g> Add<&'b $rhs> for $lhs {
      type Output = $out;
      fn add(self, rhs: &'b $rhs) -> $out {
        &self + rhs
      }
    }

    impl<'a, G: $g> Add<$rhs> for &'a $lhs {
      type Output = $out;
      fn add(self, rhs: $rhs) -> $out {
        self + &rhs
      }
    }

    impl<G: $g> Add<$rhs> for $lhs {
      type Output = $out;
      fn add(self, rhs: $rhs) -> $out {
        &self + &rhs
      }
    }
  };
}

macro_rules! define_add_assign_variants {
  (G = $g:path, LHS = $lhs:ty, RHS = $rhs:ty) => {
    impl<G: $g> AddAssign<$rhs> for $lhs {
      fn add_assign(&mut self, rhs: $rhs) {
        *self += &rhs;
      }
    }
  };
}

define_add_assign_variants!(G = Group, LHS = Commitment<G>, RHS = Commitment<G>);
define_add_variants!(G = Group, LHS = Commitment<G>, RHS = Commitment<G>, Output = Commitment<G>);

/// Provides a commitment engine
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommitmentEngine<G: Group> {
  _p: PhantomData<G>,
}

impl<G: Group> CommitmentEngineTrait<G> for CommitmentEngine<G> {
  type CommitmentKey = CommitmentKey<G>;
  type Commitment = Commitment<G>;

  fn setup(label: &'static [u8], n: usize) -> Self::CommitmentKey {
    Self::CommitmentKey {
      ck: G::from_label(label, n.next_power_of_two()),
      _p: Default::default(),
    }
  }

  fn commit(ck: &Self::CommitmentKey, v: &[G::Scalar]) -> Self::Commitment {
    assert!(ck.ck.len() >= v.len());
    Commitment {
      comm: G::vartime_multiscalar_mul(v, &ck.ck[..v.len()]),
    }
  }
}

pub(crate) trait CommitmentKeyExtTrait<G: Group> {
  type CE: CommitmentEngineTrait<G>;

  /// Splits the commitment key into two pieces at a specified point
  fn split_at(&self, n: usize) -> (Self, Self)
  where
    Self: Sized;

  /// Combines two commitment keys into one
  fn combine(&self, other: &Self) -> Self;

  /// Folds the two commitment keys into one using the provided weights
  fn fold(&self, w1: &G::Scalar, w2: &G::Scalar) -> Self;

  /// Scales the commitment key using the provided scalar
  fn scale(&self, r: &G::Scalar) -> Self;

  /// Reinterprets commitments as commitment keys
  fn reinterpret_commitments_as_ck(
    c: &[<<<Self as CommitmentKeyExtTrait<G>>::CE as CommitmentEngineTrait<G>>::Commitment as CommitmentTrait<G>>::CompressedCommitment],
  ) -> Result<Self, NovaError>
  where
    Self: Sized;
}

impl<G: Group> CommitmentKeyExtTrait<G> for CommitmentKey<G> {
  type CE = CommitmentEngine<G>;

  fn split_at(&self, n: usize) -> (CommitmentKey<G>, CommitmentKey<G>) {
    (
      CommitmentKey {
        ck: self.ck[0..n].to_vec(),
        _p: Default::default(),
      },
      CommitmentKey {
        ck: self.ck[n..].to_vec(),
        _p: Default::default(),
      },
    )
  }

  fn combine(&self, other: &CommitmentKey<G>) -> CommitmentKey<G> {
    let ck = {
      let mut c = self.ck.clone();
      c.extend(other.ck.clone());
      c
    };
    CommitmentKey {
      ck,
      _p: Default::default(),
    }
  }

  // combines the left and right halves of `self` using `w1` and `w2` as the weights
  // 将commitmentKey 折叠
  fn fold(&self, w1: &G::Scalar, w2: &G::Scalar) -> CommitmentKey<G> {
    let w = vec![*w1, *w2];
    let (L, R) = self.split_at(self.ck.len() / 2);

    let ck = (0..self.ck.len() / 2)
      .into_par_iter()
      .map(|i| {
        let bases = [L.ck[i].clone(), R.ck[i].clone()].to_vec();
        G::vartime_multiscalar_mul(&w, &bases).preprocessed()
      })
      .collect();

    CommitmentKey {
      ck,
      _p: Default::default(),
    }
  }

  /// Scales each element in `self` by `r`
  fn scale(&self, r: &G::Scalar) -> Self {
    let ck_scaled = self
      .ck
      .clone()
      .into_par_iter()
      .map(|g| G::vartime_multiscalar_mul(&[*r], &[g]).preprocessed())
      .collect();

    CommitmentKey {
      ck: ck_scaled,
      _p: Default::default(),
    }
  }

  /// 将 &[CompressedCommitment<G>] 切片重新解释为一个 CommitmentKey<G> 对象。CompressedCommitment<G> 表示压缩的椭圆曲线点，这个函数首先将切片中的每个元素解压缩为 Commitment<G> 类型的值，再将这些点预处理为 G::Prepared 类型的值，最后将它们存储在一个 CommitmentKey<G> 对象中作为密钥 ck 的一部分，并返回该对象。
  /// reinterprets a vector of commitments as a set of generators
  fn reinterpret_commitments_as_ck(c: &[CompressedCommitment<G>]) -> Result<Self, NovaError> {
    let d = (0..c.len())
      .into_par_iter()
      .map(|i| Commitment::<G>::decompress(&c[i]))
      .collect::<Result<Vec<Commitment<G>>, NovaError>>()?;
    let ck = (0..d.len())
      .into_par_iter()
      .map(|i| d[i].comm.preprocessed())
      .collect();
    Ok(CommitmentKey {
      ck,
      _p: Default::default(),
    })
  }
}
