//! `string_calc` is a collection of utilities to perform checked arithmetics on
//! &str, to counter against floating point errors. It supports (checked) addition, 
//! subtraction, and multiplication. It does not support division due to the 
//! nature of division's ability to generate infinite amount of decimals. 
//! 
//! If your calculations have too many decimal points such that it can't fit u128 
//! range AFTER calculation, it'll raise an error. 
//! If you pass in weird values that's not integer or floats/decimals, it'll raise an error. 
//! Return result will be Ok(String) which you can call .unwrap() or other methods to get
//! its internal value, if everything goes right. 

use std::cmp;

/// Perform checked_add on floating points. 
/// Inherits the "checked_add" property of rust in integers. 
/// When failed, it'll return Err(message). Success, Ok(value). 
/// 
/// NOTE: Must use basic numbers UTF-8 or it'll fail. 
/// 
/// Example: 
/// ```
/// let lhs = "172.28";
/// let rhs = "192.168";
/// 
/// assert_eq!(string_calc::checked_add(lhs, rhs).unwrap(), 
///   "364.448".to_owned());
/// ``` 
pub fn checked_add(lhs: &str, rhs: &str) -> Result<String, &'static str> {
  // Check for longest decimals. We find the "dot index"
  let res = check_str(lhs);
  let res2 = check_str(rhs);
  if res.is_err() { return Err("LHS is invalid decimal. Please check."); }
  if res2.is_err() { return Err("RHS is invalid decimal. Please check."); }

  let (lhs_u128, rhs_u128, max_decimal) = convert_to_u128(lhs, rhs);

  let value = lhs_u128.checked_add(rhs_u128);
  if value.is_none() { return Err("Sorry, u128 add encounters overflow. Please find other methods to add."); }

  // Add back the decimal points. 
  let mut value_str: String = value.unwrap().to_string();
  if max_decimal != 0 { value_str.insert(value_str.len() - max_decimal, '.') };

  return Ok(value_str);
}


/// Performs checked_sub on floating points. 
/// Inherits the checked_sub property of rust in integers. 
/// When failed, it'll return Err(message). Success, Ok(value). 
/// 
/// NOTE: Must use basic numbers UTF-8 or it'll fail. 
/// 
/// Example: 
/// ```
/// let lhs = "192.168";
/// let rhs = "172.28";
/// 
/// assert_eq!(string_calc::checked_sub(lhs, rhs).unwrap(),
///   "19.888".to_owned());
/// ``` 
pub fn checked_sub(lhs: &str, rhs: &str) -> Result<String, &'static str> {
  let res = check_str(lhs);
  let res2 = check_str(rhs);
  if res.is_err() { return Err("LHS is invalid decimal. Please check."); }
  if res2.is_err() { return Err("RHS is invalid decimal. Please check."); }

  let (lhs_u128, rhs_u128, max_decimal) = convert_to_u128(lhs, rhs);

  let value = lhs_u128.checked_sub(rhs_u128);
  if value.is_none() { return Err("Sorry, u128 add encounters overflow. Please find other methods to add."); }

  // Add back the decimal points. 
  let mut value_str: String = value.unwrap().to_string();
  if max_decimal != 0 { value_str.insert(value_str.len() - max_decimal, '.') };

  return Ok(value_str);
}

/// Performs checked_mul on floating points. 
/// Inherits the checked_mul property of rust in integers. 
/// When failed, it'll return Err(message). Success, Ok(value). 
/// 
/// NOTE: Must use basic numbers UTF-8 or it'll fail. 
/// 
/// Example: 
/// ```
/// let lhs = "12.35";
/// let rhs = "15.6";
/// 
/// assert_eq!(string_calc::checked_mul(lhs, rhs).unwrap(),
///   "192.66".to_owned());
/// ```
pub fn checked_mul(lhs: &str, rhs: &str) -> Result<String, &'static str> {
  let res = check_str(lhs);
  let res2 = check_str(rhs);
  if res.is_err() { return Err("LHS is invalid decimal. Please check."); }
  if res2.is_err() { return Err("RHS is invalid decimal. Please check."); }

  let (lhs_u128, rhs_u128, max_decimal) = convert_to_u128(lhs, rhs);
  let total_decimal = max_decimal.checked_mul(2)
    .expect("Please report Bug: Failed to multiply total_decimal. ");

  let value = lhs_u128.checked_mul(rhs_u128);
  if value.is_none() { return Err("Sorry, u128 add encounters overflow. Please find other methods to add."); }

  // Add back decimal points. 
  let mut value_str: String = value.unwrap().to_string();
  if total_decimal != 0 { 
    value_str.insert(value_str.len() - total_decimal, '.');
    value_str = value_str.trim_end_matches("0").to_owned();
  };
  value_str = value_str.trim_end_matches(".").to_owned();  // if last value is '.', trim. 

  return Ok(value_str)
}




// ==========================================================================
fn check_str(str: &str) -> Result<(), &'static str> {
  let mut dot_count = 0;
  for c in str.chars() {
    if !['0', '1', '2', '3', '4', '5', '6', 
      '7', '8', '9', '.'].contains(&c) 
    {
      return Err("Invalid String. Must be numbers and decimal point only.");
    }

    if c == '.' { dot_count += 1; }
    if dot_count > 1 { return Err("Invalid String. Cannot have more than one decimal."); }
  }
  return Ok(());
}

/// Get the decimal point given a string. 
/// di stands for dot index. 
/// So 12 will return 0, while 12.1 will return 1. 
fn get_decimal_points(num: &str) -> usize {
  let num_len = num.len();
  let num_di = num.find(".").unwrap_or(num_len - 1);
  return num_len - (num_di + 1);
}

/// Preprocess the value by: 
/// 1. Remove the dot. 
/// 2. Add appropriate number of zeros at the back. 
/// 
/// curr_d = current decimals. NEED TO PASS IN CORRECT VALUE OR FAILED.
/// Use cache value because it won't refigure it out, which waste computing power.
fn preprocess_value(num: &str, curr_d: usize, max_d: usize) -> String {
  let mut num_str = num.to_owned();
  let num_di = num.find(".");
  if num_di.is_some() { num_str.remove(num_di.unwrap()); }

  // Add zeros where appropriate
  let repeat_no = max_d - curr_d;
  if repeat_no >= 1 {
    for _ in 0..repeat_no {
      num_str.push('0');
    }
  }

  return num_str;
}

fn convert_to_u128(lhs: &str, rhs: &str) -> (u128, u128, usize) {
  let lhs_decimals = get_decimal_points(lhs);
  let rhs_decimals = get_decimal_points(rhs);
  let max_decimal = cmp::max(lhs_decimals, rhs_decimals);

  // Remove the dot. 
  let lhs_int = preprocess_value(lhs, lhs_decimals, max_decimal);
  let rhs_int = preprocess_value(rhs, rhs_decimals, max_decimal);

  let lhs_u128: u128 = lhs_int.parse().unwrap();
  let rhs_u128: u128 = rhs_int.parse().unwrap();

  return (lhs_u128, rhs_u128, max_decimal);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alphabets_wont_work() {
      let result = check_str("123str");
      assert!(result.is_err());
    }

    #[test]
    fn test_char_wont_work() {
      let result = check_str("我爱你");
      assert!(result.is_err());
    }

    #[test]
    fn test_floats_work() {
      let result = check_str("12.376");
      assert!(result.is_ok());
    }

    #[test]
    fn test_ip_addr_not_work() {
      let result = check_str("192.168.10.1");
      assert!(result.is_err());
    }

    #[test]
    fn correct_decimal() {
      let decimal = get_decimal_points("12.376");
      assert_eq!(decimal, 3);
    }

    #[test]
    fn correct_integer() {
      let decimal = get_decimal_points("123");
      assert_eq!(decimal, 0);
    }

    #[test]
    fn preprocess_value_case_1() {
      let value = preprocess_value("12.237", 3, 3);
      assert_eq!(value, "12237");
    }

    #[test]
    fn preprocess_value_case_2() {
      let value = preprocess_value("12.237", 3, 5);
      assert_eq!(value, "1223700");
    }

    #[test]
    fn preprocess_value_case_3() {
      let value = preprocess_value("12", 0, 3);
      assert_eq!(value, "12000");
    }

    #[test]
    fn preprocess_value_case_4() {
      let value = preprocess_value("12", 0, 0);
      assert_eq!(value, "12");
    }

    #[test]
    fn checked_add_case_1() {
      let value = checked_add("12.32", "15.6");
      assert_eq!(value.unwrap(), "27.92".to_owned());
    }

    #[test]
    fn checked_add_case_2() {
      let value = checked_add("12.3", "17");
      assert_eq!(value.unwrap(), "29.3".to_owned());
    }

    #[test]
    fn checked_add_case_3() {
      let value = checked_add("12", "15");
      assert_eq!(value.unwrap(), "27".to_owned());
    }

    #[test]
    fn checked_add_case_4() {
      let value = checked_add("meh", "12");
      assert!(value.is_err());
    }

    #[test]
    fn checked_add_case_5() {
      let value = checked_add("12", "meh");
      assert!(value.is_err());
    }

    // not sure if we can test overflow or not for addition; 
    // but certainly can do for multiplication. 

    #[test]
    fn checked_sub_case_1() {
      let value = checked_sub("12.367", "9.3");
      assert_eq!(value.unwrap(), "3.067".to_owned());
    }

    #[test]
    fn checked_sub_case_2() {
      let value = checked_sub("12", "6.3");
      assert_eq!(value.unwrap(), "5.7".to_owned());
    }

    #[test]
    fn checked_sub_case_3() {
      let value = checked_sub("12", "6");
      assert_eq!(value.unwrap(), "6".to_owned());
    }

    #[test]
    fn checked_sub_case_4() {
      let value = checked_sub("meh", "6");
      assert!(value.is_err());
    }

    #[test]
    fn checked_sub_case_5() {
      let value = checked_sub("6", "meh");
      assert!(value.is_err());
    }

    #[test]
    fn checked_mul_case_1() {
      let value = checked_mul("19.87", "13.625");
      assert_eq!(value.unwrap(), "270.72875".to_owned());
    }

    #[test]
    fn checked_mul_case_2() {
      let value = checked_mul("12.3", "6");
      let value2 = checked_mul("6", "12.3");
      assert_eq!(value.clone().unwrap(), "73.8".to_owned());
      assert_eq!(value.unwrap(), value2.unwrap());
    }

    #[test]
    fn checked_mul_case_3() {
      let value = checked_mul("12.5", "6");
      assert_eq!(value.unwrap(), "75".to_owned());
    }

    #[test]
    fn checked_mul_case_4() {
      let value = checked_mul("meh", "6");
      assert!(value.is_err());
    }

    #[test]
    fn checked_mul_case_5() {
      let value = checked_mul("6", "meh");
      assert!(value.is_err());
    }
}