use std::env;

mod mmdb;
mod parser;

fn main() {
  let args: Vec<String> = env::args().collect();
  if args.len() != 2 {
    return;
  }
  let fname = &args[1];
  let mut parser = parser::Parser::new(fname).unwrap();
  let mmdb = parser.parse();
  // parser.display_asserts();
  // mmdb.print_mm();
  mmdb.test_proof_graph();
  // parser.get_assert_types();

  // let mut rng = rand::thread_rng();
  // let choices = t_to_assert.get(t).unwrap();
  // let base_id = rng.gen_range(0..parser.asserts.len());
  // let assert = &parser.asserts[base_id];
  // parser.create_random_assertion(String::new("xyz"), )

  // println!("success!");
}
