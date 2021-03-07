use std::{
  convert::TryInto,
  ops::{Add, Sub},
};

#[derive(Clone, Debug)]
struct BigUint {
  data: Vec<u8>,
}

impl BigUint {
  pub fn new() -> Self {
    Self {
      data: Vec::with_capacity(16),
    }
  }

  pub fn from<T: TryInto<u128> + Copy>(init: T) -> Self {
    let mut s = BigUint::new();

    let mut value = as_u128(init);

    loop {
      s.data.push((value & 255) as u8);
      value >>= 8;

      if value == 0 {
        break;
      }
    }

    s
  }

  fn get_lower(&self) -> u128 {
    let mut bytes = self.data.iter().enumerate();

    let mut long = 0;
    let mut shift_count = 0;

    while let Some((i, byte)) = bytes.next() {
      long = long | ((byte & 255) as u128) << i * 8;
      shift_count += 1;

      if shift_count == 16 {
        return long;
      }
    }

    long
  }

  fn as_u128_vec(&self) -> Vec<u128> {
    let mut res = Vec::with_capacity(self.data.len() / 8);

    let mut bytes = self.data.iter().enumerate();

    let mut long = 0;

    let mut shift_count = 0;

    while let Some((i, byte)) = bytes.next() {
      long = long | ((byte & 255) as u128) << i * 8;
      shift_count += 1;

      if shift_count == 16 {
        res.push(long);
        long = 0;
        shift_count = 0;
      }
    }

    res
  }
}

#[inline(always)]
fn as_u128<T: TryInto<u128> + Copy>(v: T) -> u128 {
  match (v).try_into() {
    Ok(v) => v,
    _ => 0,
  }
}

impl Add<BigUint> for BigUint {
  type Output = BigUint;

  fn add(self, rhs: BigUint) -> Self::Output {
    let (mut longest, mut shortest) = if self.data.len() >= rhs.data.len() {
      (self.data, rhs.data)
    } else {
      (rhs.data, self.data)
    };

    let mut carry = 0;

    let mut byte_idx = 0_usize;

    while let Some(byte) = shortest.get_mut(byte_idx) {
      let a = *byte as u16;
      let b = *longest.get_mut(byte_idx).unwrap() as u16;

      let res = a + b + carry as u16;

      *byte = (res & 255) as u8;
      carry = (res > 255) as u8;

      byte_idx += 1;
    }

    while let Some(byte) = longest.get(byte_idx) {
      let res = *byte as u16 + carry as u16;

      let byte = (res & 255) as u8;
      carry = (res > 255) as u8;

      byte_idx += 1;
      shortest.push(byte);
    }

    if carry != 0 {
      shortest.push(1);
    }

    BigUint { data: shortest }
  }
}

impl<T: TryInto<u128> + Copy> Add<T> for BigUint {
  type Output = BigUint;

  fn add(mut self, rhs: T) -> Self::Output {
    let mut rhs = as_u128(rhs);

    let mut carry = 0;

    let mut byte_idx = 0_usize;

    while let Some(byte) = self.data.get_mut(byte_idx) {
      let a = *byte as u16;
      let b = (rhs & 255) as u16;

      let res = a + b + carry as u16;

      *byte = (res & 255) as u8;
      carry = (res > 255) as u8;

      rhs >>= 8;

      byte_idx += 1;
    }

    rhs += carry as u128;

    while rhs > 0 {
      let byte = (rhs & 255) as u8;
      self.data.push(byte);
      rhs >>= 8;
    }

    self
  }
}

impl<T: TryInto<u128> + Copy> Sub<T> for BigUint {
  type Output = BigUint;

  fn sub(mut self, rhs: T) -> Self::Output {
    let mut rhs = as_u128(rhs);

    if self <= rhs {
      return BigUint::from(0);
    }

    let mut ptr = self.data.as_mut_ptr();

    unsafe {
      for _ in 0..self.data.len() {
        let byte = ptr;

        let a = *byte as u16;
        let b = (rhs & 255) as u16;

        let res = if b <= a {
          a - b
        } else {
          // we need to borrow

          let mut next_byte = ptr.offset(1);

          loop {
            if *next_byte > 0 {
              *next_byte -= 1;
              break;
            } else {
              *next_byte = 255;
              next_byte = next_byte.offset(1);
            }
          }

          (a + 256) - b
        };

        *byte = (res & 255) as u8;

        rhs >>= 8;
        ptr = ptr.offset(1);
      }
    }

    // while rhs > 0 {
    //   let byte = (rhs & 255) as u8;
    //   self.data.push(byte);
    // }

    self
  }
}

impl<T: TryInto<u128> + Copy> PartialOrd<T> for BigUint {
  fn partial_cmp(&self, other: &T) -> Option<std::cmp::Ordering> {
    let other = as_u128(*other);

    match self.get_lower().partial_cmp(&other) {
      Some(a) => {
        match a {
          std::cmp::Ordering::Less => {
            // lower is less than num, so we need to check the u128 vec
            match self.as_u128_vec().get(1) {
              Some(next_group) => next_group.partial_cmp(&other),
              None => Some(a),
            }
          }
          _ => Some(a),
        }
      }
      None => None,
    }
  }
}

impl PartialEq for BigUint {
  fn eq(&self, other: &Self) -> bool {
    self.data.eq(&other.data)
  }
}

impl<T: TryInto<u128> + Copy> PartialEq<T> for BigUint {
  fn eq(&self, rhs: &T) -> bool {
    let rhs = as_u128(*rhs);

    let mut high: u128 = 0;
    let mut low: u128 = 0;

    let mut data = self.data.iter().enumerate();

    while let Some((i, byte)) = data.next() {
      low = low | ((byte & 255) as u128) << (i * 8);
    }

    while let Some((i, byte)) = data.next() {
      high = high | ((byte & 255) as u128) << (i * 8);
    }

    high == 0 && low == rhs
  }
}

#[cfg(test)]
mod tests {

  use rand::Rng;

  use super::*;

  #[test]
  fn u256_can_be_created() {
    let _ = BigUint::new();
  }

  #[test]
  fn creation_is_accurate() {
    let mut lim = 500_000;

    let mut rng = rand::thread_rng();

    while lim > 0 {
      let r = rng.gen_range(1_u128..=u128::MAX);
      assert_eq!(BigUint::from(r), r);
      lim -= 1;
    }
  }

  #[test]
  fn u256_equals_u128() {
    let big_num = BigUint::from(u128::MAX);

    assert_eq!(big_num, u128::MAX);
  }

  #[test]
  fn as_u128_vec_works() {
    assert_eq!(BigUint::from(u128::MAX).as_u128_vec(), vec![u128::MAX]);
    assert_eq!(
      BigUint::from(u128::MAX / 2).as_u128_vec(),
      vec![u128::MAX / 2]
    );
  }

  #[test]
  fn add_works() {
    let mut big_num = BigUint::from(0);

    big_num = big_num + 1;

    assert_eq!(big_num, 1);
  }

  #[test]
  fn add_works_range() {
    let mut big_num = BigUint::from(0);
    let mut val: u128 = 0;

    for _ in 0..500_000 {
      val += 1;
      big_num = big_num + 1;

      assert_eq!(big_num, val);
    }
  }

  #[test]
  fn add_works_fuzz() {
    assert_eq!(BigUint::from(255), 255);
    assert_eq!(BigUint::from(256), 256);
    assert_eq!(BigUint::from(0) + 256, 256);
    assert_eq!(BigUint::from(255) + 1, BigUint::from(256));

    let mut rng = rand::thread_rng();

    for _ in 0..500_000 {
      let a = rng.gen_range(1..=2_u64.pow(63));
      let b = rng.gen_range(1..=2_u64.pow(63));

      assert_eq!(BigUint::from(a + b), a + b);
      assert_eq!(BigUint::from(a) + BigUint::from(b), BigUint::from(a + b));
    }
  }

  #[test]
  fn sub_works() {
    assert_eq!(BigUint::from(10) - 10, 0);
    assert_eq!(BigUint::from(10) - 11, 0);
    assert_eq!(BigUint::from(10) - 1, 9);
  }

  #[test]
  fn sub_works_range() {
    let mut big_num = BigUint::from(u128::MAX);
    let mut val = u128::MAX;

    for i in 0..500_000 {
      val -= 1;
      big_num = big_num - 1;

      assert_eq!(big_num, val);
    }
  }

  #[test]
  fn sub_works_fuzz() {
    assert_eq!(BigUint::from(0) - 256, 0);
    assert_eq!(BigUint::from(255) - 1, 254);
    assert_eq!(BigUint::from(130_000) - 1, 129_999);
    assert_eq!(BigUint::from(130_000) - 1, BigUint::from(129_999));

    let mut rng = rand::thread_rng();

    for _ in 0..500_000 {
      let a = rng.gen_range(2_u64.pow(32)..=2_u64.pow(63));
      let b = rng.gen_range(1..=2_u64.pow(31));

      assert_eq!(BigUint::from(a - b), a - b);
      // assert_eq!(BigUint::from(a) - BigUint::from(b), BigUint::from(a - b));
    }
  }
}
