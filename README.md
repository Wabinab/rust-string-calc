# String Calculation for Rust
Using `&str` or `String` to perform calculations: addition, subtraction, and multiplication. Floating points calculation tends to have floating point errors, therefore, you either want to use decimals or integers. Here, we use integers instead of decimals. 

Reasons: First, if you know how expensive it is to perform calculation and store values on web3, you'd know why. Second, sometimes, it doesn't work with some dependencies. For example, crates that generate random number that depends on computer state didn't work a year ago (didn't check nowadays if they allow it), to protect host computer probably. So, this crate is written without dependencies other than pure rust internal libraries. 

## Usage: 

You can do addition, subtraction, and multiplication with the crate. Here are some examples. 

```rust
use string_calc::{checked_add, checked_sub, checked_mul};

pub fn main() {
  let lhs = "15.6";
  let rhs = "12.35".to_owned();

  let value_add: Result<String, &'static str> = checked_add(lhs, rhs);
  let value_sub: Result<String, &'static str> = checked_sub(lhs, rhs);
  let value_mul: Result<String, &'static str> = checked_mul(lhs, rhs);
  let value_compare: Result<bool, &'static str> = compare(lhs, rhs, "gt");

  // Negative numbers are also supported. 
  // And output results can be in negative form.
  let lhs = "-12.3".to_owned();
  let rhs = "2.8";

  let value_add1: Result<String, &'static str> = checked_add(lhs, rhs);

  // And if you want to sum an array/vector
  let our_vec = vec!["12.432", "18.37", "21"];
  let sum_of_our_vec: Result<String, &'static str> = sum(our_vec);
}
```

