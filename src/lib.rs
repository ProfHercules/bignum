use std::{
  fmt::Display,
  ops::{Add, AddAssign, Sub},
};

#[derive(Debug, Clone)]
pub struct BigUint {
  data: Vec<u8>,
}

fn num_to_vec(mut n: u128) -> Vec<u8> {
  let mut res = Vec::new();

  let mut combine = false;

  while n > 0 {
    let mut nibble = ((n % 10) as u8) << 4;

    if combine {
      if let Some(prev) = res.pop() {
        nibble = prev | (nibble >> 4);
      }
    }
    combine = !combine;

    res.push(nibble);

    n /= 10;
  }

  res
}

impl BigUint {
  pub fn new(init: u128) -> Self {
    BigUint {
      data: num_to_vec(init),
    }
  }
}

fn vec_add(left: &Vec<u8>, right: &Vec<u8>) -> Vec<u8> {
  let mut result = Vec::new();

  let (mut l, mut s) = if left.len() >= right.len() {
    (left.iter(), right.iter())
  } else {
    (right.iter(), left.iter())
  };

  let mut carry: u8 = 0;

  while let Some(b) = s.next() {
    let a = l.next().unwrap();

    let high_res = (a >> 4) as u16 + (b >> 4) as u16 + carry as u16;

    let high_sum = (high_res % 10) as u8;
    let high_carry = (high_res > 9) as u8;

    let low_res = (a & 0b1111) as u16 + (b & 0b1111) as u16 + high_carry as u16;
    let low_sum = (low_res % 10) as u8;
    carry = (low_res > 9) as u8;

    let sum = (high_sum << 4) + (low_sum);

    result.push(sum);
  }

  result
}

// fn vec_sub(left: &Vec<u8>, right: &Vec<u8>) -> Vec<u8> {
//   let mut result = Vec::new();

//   let (mut l, mut s) = if left.len() >= right.len() {
//     (left.iter().peekable(), right.iter().peekable())
//   } else {
//     (right.iter().peekable(), left.iter().peekable())
//   };

//   while let Some(b) = s.next() {
//     let a = l.next().unwrap();

//     let high_res = (a >> 4) as u16 + (b >> 4) as u16 + carry as u16;

//     let high_sum = (high_res % 10) as u8;
//     let high_carry = (high_res > 9) as u8;

//     let low_res = (a & 0b1111) as u16 + (b & 0b1111) as u16 + high_carry as u16;
//     let low_sum = (low_res % 10) as u8;
//     carry = (low_res > 9) as u8;

//     let sum = (high_sum << 4) + (low_sum);

//     result.push(sum);
//   }

//   result
// }

impl Add for BigUint {
  type Output = Self;

  fn add(self, other: Self) -> Self::Output {
    let result = vec_add(&self.data, &other.data);

    Self { data: result }
  }
}

impl Sub for BigUint {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output {
    todo!()
  }
}

impl AddAssign for BigUint {
  fn add_assign(&mut self, other: Self) {
    let result = vec_add(&self.data, &other.data);

    *self = Self { data: result }
  }
}

// impl Mul for BigUint {
//   type Output = Self;

//   fn mul(self, other: Self) -> Self::Output {
//     // bad approach

//     let mut res = Vec::new();

//     let mut multiplier = other.clone();

//     while multiplier > 0 {
//       // do something
//       println!("{}", multiplier);
//       multiplier -= 1;
//     }

//     BigUint { data: res }
//   }
// }

impl PartialEq for BigUint {
  fn eq(&self, other: &Self) -> bool {
    self.data.eq(&other.data)
  }
}

impl PartialEq<u128> for BigUint {
  fn eq(&self, other: &u128) -> bool {
    self.data.eq(&num_to_vec(*other))
  }
}

impl PartialOrd<u128> for BigUint {
  fn partial_cmp(&self, other: &u128) -> Option<std::cmp::Ordering> {
    self.data.partial_cmp(&num_to_vec(*other))
  }
}

impl Display for BigUint {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut digits = self.data.iter().rev();

    let mut res = String::from("");

    let mut skip_leading_zero = true;

    while let Some(dig) = digits.next() {
      let low = dig & 0b1111;

      if skip_leading_zero && low == 0 {
        res = format!("{}{}", res, dig >> 4);
      } else {
        res = format!("{}{}{}", res, low, dig >> 4);
      }

      skip_leading_zero = false;
    }

    write!(f, "{}", res)
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  #[test]
  fn num_to_vec_works_8bit() {
    let num = 8;
    let manual_vec = vec![128];
    let nvec = num_to_vec(num);
    assert_eq!(manual_vec, nvec);
  }

  fn vec_to_num(v: &mut Vec<u8>) -> usize {
    let mut n: usize = 0;
    let mut len = v.len() * 2;
    let mut push = true;

    while len > 0 {
      if let Some(val) = v.pop() {
        let dig = val & 0b1111;
        let next_dig = val >> 4;

        if push {
          v.push(next_dig);
        }
        push = !push;

        n += dig as usize;
        if v.last().is_some() {
          n *= 10;
        }
      }
      len -= 1;
    }

    n
  }

  #[test]
  fn num_to_vec_works_16bit() {
    assert_eq!(vec![137, 32], num_to_vec(298));
    assert_eq!(vec![36, 48], num_to_vec(342));
    assert_eq!(vec![4, 96], num_to_vec(640));

    assert_eq!(298, vec_to_num(&mut num_to_vec(298)));
    assert_eq!(13276, vec_to_num(&mut num_to_vec(13276)));
    assert_eq!(9_374_892, vec_to_num(&mut num_to_vec(9_374_892)));
  }

  #[test]
  fn big_uint_init() {
    let _ = BigUint::new(255);
  }

  #[test]
  fn big_uint_massive() {
    let a = BigUint::new(u128::MAX);
    let a2 = a.clone() + a.clone();

    println!("---------------------------------------------------------");
    println!("u128::MAX =                     {}", u128::MAX);
    println!("BigUint::new(usize::MAX) =      {}", a);
    println!("BigUint::new(usize::MAX) x 2 =  {}", a2);
    println!("---------------------------------------------------------");
  }

  #[test]
  fn big_uint_add_basic() {
    let big_a = BigUint::new(298);
    let big_b = BigUint::new(342);

    let sum = big_a + big_b;

    assert_eq!(sum, BigUint::new(640));
  }

  #[test]
  fn big_uint_add() {
    let e = 2_u128.pow(16);
    let s = e - 500;

    for a in s..=e {
      for b in s..=e {
        let big_a = BigUint::new(a);
        let big_b = BigUint::new(b);

        let sum = big_a + big_b;

        if sum != BigUint::new(a + b) {
          println!("{:16b} + {:16b} = {:16b}", a, b, a + b);
          println!(
            "{:?} + {:?} = {:?}",
            num_to_vec(a),
            num_to_vec(b),
            num_to_vec(a + b)
          );
        }

        assert_eq!(sum, BigUint::new(a + b));
      }
    }
  }

  #[test]
  fn big_uint_sub_basic() {
    let big_a = BigUint::new(298);
    let big_b = BigUint::new(342);

    let diff = big_b - big_a;

    assert_eq!(diff, BigUint::new(44));
  }
  // #[test]
  // fn big_uint_add_large() {
  //   let mut big = BigUint::new(1);
  //   let one = BigUint::new(1);

  //   println!("{}", big);

  //   loop {
  //     big += one.clone();

  //     println!("{}", big);

  //     sleep(Duration::from_millis(100))
  //   }
  // }
}
