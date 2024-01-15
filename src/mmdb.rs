use std::collections::{ HashMap, HashSet, VecDeque };
use std::fmt::format;
use std::io::prelude::*;

use rand::prelude::*;

#[derive(Clone, PartialEq, Eq)]
pub enum Word {
  Var(u32),
  Const(u32),
}

#[derive(Clone)]
pub struct Sentence {
  pub t: u32,
  pub words: Vec<Word>,
}

impl Sentence {
  pub fn new(t: u32) -> Sentence {
    return Sentence {
      t: t,
      words: Vec::new(),
    };
  }
}

#[derive(Clone)]
pub struct VarDecl {
  pub t: u32, // type id
  pub var: u32, // var id
}

#[derive(Clone)]
pub enum Hypothesis {
  F(VarDecl),
  E(Sentence),
}

impl Hypothesis {
  fn to_sentence(&self) -> Sentence {
    match self {
      Hypothesis::F(decl) =>
        Sentence {
          t: decl.t,
          words: vec![
            Word::Var(decl.var),
          ]
        },
      Hypothesis::E(sentence) => sentence.clone(),
    }
  }
}

// Proof
// a proof is a series of steps.
// each step is either saved or not.
// steps can reference a hypothesis, a dependency, or a saved step
// 
#[derive(Clone, Debug)]
pub enum ProofStep {
  Hyp(u32),
  Assert(u32),
  Var(u32),
  Saved(u32),
}

#[derive(Clone)]
struct Assertion {
  name: String,
  is_axiom: bool,

  // The assertions that the proof of this assertion depends on.
  hyps: Vec<Hypothesis>,
  disjoint_vars: Vec<(u32, u32)>,
  consequent: Sentence,

  // deps: Vec<Symbol>,
  proof: Vec<ProofStep>,
}

impl Assertion {
  fn get_mand_var_set(&self) -> HashSet<u32> {
    let mut mand_var_set = HashSet::<u32>::new();
    for hyp in self.hyps.iter() {
      match hyp {
        Hypothesis::F(decl) => { mand_var_set.insert(decl.var); },
        _ => {},
      }
    }
    return mand_var_set;
  }
  fn get_all_var_set(&self, mmdb: &MmDb) -> HashSet<u32> {
    // get mandatory vars
    let mut var_set = HashSet::<u32>::new();
    for hyp in self.hyps.iter() {
      match hyp {
        Hypothesis::F(decl) => { var_set.insert(decl.var); },
        _ => {},
      }
    }

    // get optional vars
    for step in self.proof.iter() {
      match step {
        ProofStep::Var(id) => {
          var_set.insert(*id);
        },
        _ => continue,
      }
    }

    return var_set;
  }
}

struct Var {
  name: String,
  t: u32,
}

struct Const {
  name: String,
}

struct ProofNode {
  step: ProofStep,
}

/* TODO: this could be optimized, as we know that once a node
 * has been added, it will never have edges added. I.e., each node
 * has a fixed number of edges, though a node when being added could
 * have any number of edges. 
 * the optimization would be to make edges not a Vec<Vec<usize>>,
 * but Vec<usize>, with each node storing the number of hypotheses,
 * and the start of the hypotheses within the Vec.
 */
struct ProofGraph {
  nodes: Vec<ProofNode>,
  root: usize,
  edges: Vec<Vec<usize>>,
}

impl ProofGraph {
  fn pretty_print(&self) {
    println!("root: {}", self.root);
    println!("nodes:");
    for (i, node) in self.nodes.iter().enumerate() {
      println!("{:>4}: {:?}", i, node.step);
    }
    println!("edges:");
    for (i, neighbors) in self.edges.iter().enumerate() {
      print!("{:>4}: [", i);
      for neighbor in neighbors.iter() {
        print!(" {},", neighbor);
      }
      println!(" ]");
    }
  }

  fn add_node(&mut self, node: ProofNode) -> usize {
    let node_id = self.nodes.len();
    self.nodes.push(node);
    self.edges.push(vec![]);
    return node_id;
  }

  fn add_node_with_edges(&mut self, node: ProofNode, dsts: &[usize]) -> usize {
    let node_id = self.nodes.len();
    self.nodes.push(node);
    self.edges.push(dsts.to_vec());
    return node_id;
  }

  fn from_theorem(mmdb: &MmDb, theorem: &Assertion) -> ProofGraph {
    let mut graph = ProofGraph {
      nodes: vec![],
      root: 0,
      edges: vec![],
    };

    let mut stack = Vec::<usize>::new();
    let mut steps = Vec::<usize>::new();
    // TODO: can de-duplicate Hyps and Vars
    for step in theorem.proof.iter() {
      match step {
        ProofStep::Hyp(id) => {
          let node_id = graph.add_node(ProofNode { step: step.clone() });
          stack.push(node_id);
          steps.push(node_id);
        },
        ProofStep::Var(id) => {
          let node_id = graph.add_node(ProofNode { step: step.clone() });
          stack.push(node_id);
          steps.push(node_id);
        },
        ProofStep::Assert(id) => {
          let assert = &mmdb.asserts[*id as usize];
          if assert.hyps.len() > stack.len() {
            panic!("invalid");
          }
          let hyps_start = stack.len() - assert.hyps.len();
          let node_id = graph.add_node_with_edges(
            ProofNode { step: step.clone() },
            &stack[hyps_start..]
          );
          stack.truncate(hyps_start);
          stack.push(node_id);
          steps.push(node_id);
        },
        ProofStep::Saved(step) => {
          let node_id = steps[*step as usize];
          stack.push(node_id);
          steps.push(node_id);
        },
      }
    }
    graph.root = stack[stack.len()-1];
    return graph;
  }

  fn unfold_theorem(&mut self, node_id: usize, mmdb: &MmDb, theorem: &Assertion) {
    let hyp_src = self.edges[node_id].clone();
    self.edges[node_id].clear();

    let mut stack = Vec::<usize>::new();
    let mut steps = Vec::<usize>::new();
    for step in theorem.proof.iter() {
      match step {
        ProofStep::Hyp(id) => {
          let node_id = hyp_src[*id as usize];
          stack.push(node_id);
          steps.push(node_id);
        },
        ProofStep::Var(_) => {
          // TODO: remap?
          let node_id = self.add_node(ProofNode { step: step.clone() });
          stack.push(node_id);
          steps.push(node_id);
        },
        ProofStep::Assert(id) => {
          let assert = &mmdb.asserts[*id as usize];
          if assert.hyps.len() > stack.len() {
            panic!("invalid");
          }
          let hyps_start = stack.len() - assert.hyps.len();
          let node_id = self.add_node_with_edges(
            ProofNode { step: step.clone() },
            &stack[hyps_start..]
          );
          stack.truncate(hyps_start);
          stack.push(node_id);
          steps.push(node_id);
        },
        ProofStep::Saved(step) => {
          let node_id = steps[*step as usize];
          stack.push(node_id);
          steps.push(node_id);
        },
      }
    }
    let root = stack[stack.len()-1];
    if node_id == self.root {
      self.root = root;
    } else {
      for src_id in 0..self.nodes.len() {
        for dst_id in self.edges[src_id].iter_mut() {
          if *dst_id == node_id {
            *dst_id = root;
          }
        }
      }
    }
  }

  fn to_proof(&self) -> Vec<ProofStep> {
    let mut visited = vec![false; self.nodes.len()];
    let mut node_to_step = vec![0; self.nodes.len()];
    let mut stack = vec![(0, self.root)];
    let mut proof = Vec::<ProofStep>::new();
    // reverse topological visit
    while let Some((child_num, node)) = stack.pop() {
      if child_num < self.edges[node].len() {
        stack.push((child_num+1, node));
        let child_id = self.edges[node][child_num];
        if !visited[child_id] {
          stack.push((0, child_id));
        } else {
          proof.push(ProofStep::Saved(node_to_step[child_id]));
        }
      } else {
        visited[node] = true;
        node_to_step[node] = proof.len() as u32;
        match self.nodes[node].step {
          ProofStep::Hyp(id) => proof.push(ProofStep::Hyp(id)),
          ProofStep::Var(id) => proof.push(ProofStep::Var(id)),
          ProofStep::Assert(id) => proof.push(ProofStep::Assert(id)),
          _ => panic!("invalid"),
        }
      }
    }

    return proof;
  }
}

/**Metamath database.
 */
pub struct MmDb {
  pub vars: Vec<Var>,
  pub consts: Vec<Const>,
  pub asserts: Vec<Assertion>,
}

impl MmDb {
  pub fn new() -> MmDb {
    return MmDb {
      vars: Vec::new(),
      consts: Vec::new(),
      asserts: Vec::new(),
    }
  }

  fn get_assert<'a>(&'a self, id: u32) -> &'a Assertion {
    return &self.asserts[id as usize];
  }

  pub fn add_const(&mut self, name: String) -> u32 {
    let id = self.consts.len() as u32;
    self.consts.push(Const { name: name });
    return id;
  }

  // We impose an additional constraint that variables never have different
  // types in different scopes. Really, variable declarations should be the same
  // as floating declarations, as there is no context in which you can use a variable
  // without a type.
  pub fn add_variable(&mut self, name: String, t: u32) -> u32 {
    let id = self.vars.len() as u32;
    self.vars.push(Var { name, t });
    return id;
  }

  // pub fn add_floating(&mut self, t: u32, var: u32) -> u32 {
  //   if self.vars[var as usize].type_declared {
  //     if self.vars[var as usize].t != t {
  //       panic!("invalid");
  //     }
  //   } else {
  //     self.vars[var as usize].type_declared = true;
  //     self.vars[var as usize].t = t;
  //   }
  //   let id = self.hyps.len();
  //   self.hyps.push(Hypothesis::F(VarDecl { t, var }));
  //   return id as u32;
  // }

  // pub fn add_essential(&mut self, t: u32, syms: Vec<Symbol>) -> u32 {
  //   let id = self.hyps.len();
  //   self.hyps.push(Hypothesis::E(SymStr { t, syms }));
  //   return id as u32;
  // }

  pub fn add_axiom(&mut self,
    name: String,
    hyps: Vec<Hypothesis>,
    consequent: Sentence,
    disjoint_vars: Vec<(u32, u32)>)
    -> u32
  {
    let assert_id = self.asserts.len() as u32;
    self.asserts.push(Assertion {
      name: name,
      is_axiom: true,
      hyps: hyps,
      consequent: consequent,
      disjoint_vars: disjoint_vars,
      proof: vec![],
    });

    return assert_id;
  }

  pub fn add_theorem(&mut self,
    name: String,
    hyps: Vec<Hypothesis>,
    consequent: Sentence,
    disjoint_vars: Vec<(u32, u32)>,
    proof: Vec<ProofStep>)
    -> u32
  {
    let theorem = Assertion {
      name,
      is_axiom: false,
      hyps,
      consequent,
      disjoint_vars,
      proof,
    };

    // println!("$(");
    // println!("$( adding theorem {} $)", theorem.name);

    self.check_proof_validity(&theorem);

    let assert_id = self.asserts.len() as u32;
    self.asserts.push(theorem);

    return assert_id;
  }

  /* NOTE: we assume that all optional variables are disjoint.
   */
  /**Apply an assertion to the stack. This will pop off hypotheses for the
   * assertion and then push the assertion (with the necessary variable
   * substitutions) to the stack. It will also check that the disjoint requirements
   * of the assertion are maintained, and perform necessary type and match checking
   * for the hypotheses.
   */
  fn apply(stack: &mut Vec<Sentence>, assert: &Assertion,
    mand_vars: &HashSet<u32>,
    disjoint_vars: &HashSet<(u32, u32)>)
  {
    // check to ensure that there are enough statements on the stack to apply assert
    if stack.len() < assert.hyps.len() {
      panic!("invalid");
    }


    // construct variable map and check that the stack matches assert's
    // hypotheses
    let mut var_map: HashMap<u32, Vec<Word>> = HashMap::new();
    let hyp_start = stack.len() - assert.hyps.len();
    for i in 0..assert.hyps.len() {
      let stack_entry = &stack[hyp_start + i];
      match &assert.hyps[i] {
        Hypothesis::F(decl) => {
          if stack_entry.t != decl.t {
            panic!("invalid");
          }
          var_map.insert(decl.var, stack_entry.words.clone());
        },
        Hypothesis::E (ss)     => {
          if stack_entry.t != ss.t {
            panic!("invalid");
          }

          // TODO: unnecessary allocation?
          let mut ss_sub = Vec::<Word>::new();
          for word in ss.words.iter() {
            match word {
              Word::Var(id) => {
                let sub = var_map.get(id).unwrap();
                ss_sub.extend_from_slice(sub.as_slice());
              },
              Word::Const(id) => {
                ss_sub.push(word.clone());
              },
            }
          }

          if ss_sub.len() != stack_entry.words.len() {
            panic!("invalid");
          }
          for i in 0..ss_sub.len() {
            if ss_sub[i] != stack_entry.words[i] {
              panic!("invalid");
            }
          }
        },
      }
    }

    // Check the disjointness
    // first, construct map of variables to variables used in substitutions
    let mut var_var_map = HashMap::<u32, Vec<u32>>::new();
    let mut var_set = HashSet::<u32>::new();
    for (v, words) in var_map.iter() {
      for w in words {
        if let Word::Var(id) = w {
          var_set.insert(*id);
        }
      }
      let mut vars = Vec::<u32>::new();
      for v0 in var_set.drain() {
        vars.push(v0);
      }
      var_var_map.insert(*v, vars);
    }

    // Then, for every set of variables that must be disjoint, check that
    // their substitutions are disjoint.
    // All non-mandatory variables are disjoint.
    for (a, b) in &assert.disjoint_vars {
      for s0 in var_var_map.get(a).unwrap() {
        for s1 in var_var_map.get(b).unwrap() {
          if !mand_vars.contains(s0) || !mand_vars.contains(s1) {
            // if either is optional, and they are not the same, continue
            if *s0 == *s1 {
              panic!("invalid");
            }
            continue;
          }
          if s0 < s1 {
            if !disjoint_vars.contains(&(*s0, *s1)) {
              panic!("invalid");
            }
          } else {
            if !disjoint_vars.contains(&(*s1, *s0)) {
              panic!("invalid");
            }
          }
        }
      }
    }

    // The application is valid, drop the hypotheses from stack
    stack.truncate(hyp_start);

    // then push the substituted consequent to the stack.
    let mut consequent = Sentence::new(assert.consequent.t);
    for word in &assert.consequent.words {
      match word {
        Word::Var(id) => {
          consequent.words.extend_from_slice(var_map.get(&id).unwrap().as_slice());
        },
        Word::Const(id) => {
          consequent.words.push(word.clone());
        },
      }
    }
    stack.push(consequent);
  }

  /**NOTE: this 'should' return bool, but it is a lot easier to trace and debug stuff
   * if you just panic.
   */
  fn check_proof_validity(&self, theorem: &Assertion)
  {
    let mut disjoint_var_set = HashSet::<(u32, u32)>::new();
    for (a, b) in theorem.disjoint_vars.iter() {
      disjoint_var_set.insert((*a, *b));
    }

    let mut stack = Vec::<Sentence>::new();
    let mut saved_statements = Vec::<Sentence>::new();
    let mand_vars = theorem.get_mand_var_set();

    for (step_id, step) in theorem.proof.iter().enumerate() {
      // println!("step {:<4}: {:?}", step_id, step);
      match step {
        ProofStep::Hyp(id) => {
          let hyp = &theorem.hyps[*id as usize];
          stack.push(hyp.to_sentence());
        },
        ProofStep::Var(id) => {
          let var = &self.vars[*id as usize];
          stack.push(Sentence {t: var.t, words: vec![Word::Var(*id)] });
        },
        ProofStep::Assert(id) => {
          let assert = &self.asserts[*id as usize];
          // // DEBUG
          // let hyp_start = stack.len() - assert.hyps.len();
          // println!("stack:");
          // for i in 0..assert.hyps.len() {
          //   println!("{:>4}: {}", i, self.render_sentence(&stack[hyp_start + i]));
          // }
          // println!("assert:");
          // self.print_assert_statement(assert);
          MmDb::apply(&mut stack, assert, &mand_vars, &disjoint_var_set);
        },
        ProofStep::Saved(id) => {
          let st = saved_statements[*id as usize].clone();
          stack.push(st);
        },
      }
      // println!("top of stack: {}", self.render_sentence(&stack[stack.len()-1]));
      saved_statements.push(stack[stack.len()-1].clone());
    }

    // check that top of stack matches consequent
    if stack.len() != 1 {
      panic!("invalid");
    }
    // check that top of stack is same as assertion, then create assertion
    if theorem.consequent.words.len() != stack[0].words.len() {
      panic!("invalid");
    }
    if theorem.consequent.t != stack[0].t {
      panic!("invalid");
    }
    for i in 0..theorem.consequent.words.len() {
      if theorem.consequent.words[i] != stack[0].words[i] {
        panic!("invalid");
      }
    }
    return;
  }

  // fn permute_all_variables(&self, assert: &mut Assertion) {
  //   fn remap_ss(ss: &mut SymStr, &var_var_map: Vec<u32>) {
  //     for sym in ss.syms.iter_mut() {
  //       match sym.t {
  //         SymbolType::Var => {
  //           sym.id = var_var_map[sym.id as usize];
  //         },
  //         _ => continue,
  //       }
  //     }
  //   }

  //   // create a map that maps old variables to new variables
  //   // first, collect variables by type
  //   let mut type_to_vars = HashMap::<u32, Vec<u32>>::new();
  //   for (var_id, var) in self.vars.iter().enumerate() {
  //     if !var.type_declared {
  //       panic!("invalid");
  //     }
  //     match type_to_vars.get_mut(var.t) {
  //       Some(vars) => {
  //         vars.push(var_id);
  //       },
  //       None => {
  //         type_to_vars.insert(var.t, vec![var_id]);
  //       }
  //     }
  //   }

  //   // then permute these, within their type
  //   let mut rng = rand::thread_rng();
  //   for (_, vars) in type_to_vars.iter_mut() {
  //     vars.shuffle(&mut rng);
  //   }

  //   // then create a map for variable ids to variable ids
  //   let mut var_var_map = vec![];
  //   for (var_id, var) in self.vars.iter().enumerate() {
  //     let remapped_to = type_to_vars.get_mut(var.t).pop().unwrap();
  //     var_var_map.push(remapped_to);
  //   }

  //   // create a map that maps variables to hypotheses
  //   // TODO: this is pretty annoying, and we should just use variables
  //   // instead of hypotheses at some point.
  //   let mut var_hyp_map = vec![0; self.vars.len()];
  //   for (hyp_id, hyp) in self.hyps.iter().enumerate() {
  //     match hyp {
  //       Hypothesis::F(decl) => var_hyp_map[decl.id] = hyp_id,
  //       _ => {},
  //     }
  //   }

  //   // permute vars in deps
  //   for sym in assert.deps.iter_mut() {
  //     match sym.t {
  //       SymbolType::Hyp => {
  //         let var_id = self.hyps[sym.id as usize];
  //         match self.hyps[sym.id as usize] {
  //           Hypothesis::F(decl) => {
  //             sym.id = var_hyp_map[decl.var];
  //           },
  //           _ => panic!("invalid"),
  //         }
  //       },
  //       _ => continue,
  //     }
  //   }

  //   // permute vars in hyps
  //   for hyp in assert.hyps.iter_mut() {
  //     match hyp {
  //       Hypothesis::F(decl) => { decl.var = var_var_map[decl.var as usize]; },
  //       Hypothesis::E(ss)   => { remap_ss(ss, &var_var_map); },
  //     }
  //   }

  //   // permute vars in disjoints
  //   for (a, b) in assert.disjoint_vars.iter_mut() {
  //     a = var_var_map[a as usize];
  //     b = var_var_map[b as usize];
  //   }

  //   // permute vars in  consequent
  //   remap_ss(&mut assert.consequent, &var_var_map);
  // }

  /**Go through all optional variables of a proof, and if they are
   * in the excluded vars set, then change them to some different
   * variable.
   */
  fn remap_optional_variables(&self,
    thm: &mut Assertion,
    excluded_vars: &HashSet<u32>)
  {
    println!("$( excluded_vars.len() = {} $)", excluded_vars.len());
    let mut potential_vars = HashMap::<u32, Vec<u32>>::new();
    for (var_id, var) in self.vars.iter().enumerate() {
      let var_id = var_id as u32;
      if !excluded_vars.contains(&var_id) {
        match potential_vars.get_mut(&var.t) {
          Some(vars) => vars.push(var_id),
          None => { potential_vars.insert(var.t, vec![var_id]); },
        }
      }
    }
    // DEBUG
    for (t, vars) in potential_vars.iter() {
      println!("$( {}: vars.len() = {} $)", self.consts[*t as usize].name, vars.len());
    }
    let mut var_map = HashMap::<u32, u32>::new();
    for step in thm.proof.iter_mut() {
      match step {
        ProofStep::Var(id) => {
          match var_map.get(&id) {
            Some(new_id) => *id = *new_id,
            None => {
              // we must remap to something that ALSO EXCLUDES CURRENT LOCAL VARIABLES!
              // Otherwise, you might keep some local d -> d not in excluded variables,
              // but map some b -> d when b is in the excluded variables.
              let var = &self.vars[*id as usize];
              let new_id = potential_vars.get_mut(&var.t).unwrap().pop().unwrap();
              // println!("remapping {}: {} ({}) to {} ({})",
              //   self.consts[var.t as usize].name, 
              //   self.vars[*id as usize].name, id,
              //   self.vars[new_id as usize].name, new_id);
              var_map.insert(*id, new_id);
              *id = new_id
            }
          }
          
        },
        _ => {},
      }
    }
  }


  /**Unfolding a dependency in an assertion will remove all references
   * to that dependency in the proof and will replace them with an inlined
   * proof of the dependency.
   */
  fn unfold(&self, name: String, thm: &Assertion, to_unfold_id: u32) -> Assertion {
    if thm.is_axiom {
      panic!("invalid");
    }
    let mut to_unfold = self.asserts[to_unfold_id as usize].clone();

    if to_unfold.is_axiom {
      panic!("invalid");
      // cannot unfold a hypothesis (which must be a floating hypothesis)
      // cannot unfold an axiom
      // alternately: unfolding an axiom is a trivial operation
    }

    // sanity check -- does the theorem contain the dependency?
    let mut contains_dep = false;
    for step in thm.proof.iter() {
      match step {
        ProofStep::Assert(id) => {
          if *id == to_unfold_id {
            contains_dep = true;
            break;
          }
        },
        _ => continue,
      }
    }
    if !contains_dep {
      panic!("invalid");
    }

    let all_vars = thm.get_all_var_set(self);
    // TODO: technically, we could see all the variables that are substituted,
    // and then check the disjoint conditions, and then re-use local variables
    // if needed, but that is lot of work.
    // println!("$( remapping variables for {}:", name);
    // println!("all vars:");
    // for var_id in all_vars.iter() {
    //   println!("    {}: {}", var_id, self.vars[*var_id as usize].name);
    // }
    // println!("remapped:");
    self.remap_optional_variables(&mut to_unfold, &all_vars);
    // println!("$)");

    let mut graph = ProofGraph::from_theorem(self, &thm);
    // println!("graph before:");
    // graph.pretty_print();
    let mut nodes_to_unfold = vec![];
    for (node_id, node) in graph.nodes.iter().enumerate() {
      if let ProofStep::Assert(id) = node.step {
        if id == to_unfold_id {
          nodes_to_unfold.push(node_id);
        }
      }
    }
    for node_id in nodes_to_unfold.iter() {
      graph.unfold_theorem(*node_id, self, &to_unfold);
    }
    // println!("graph after:");
    // graph.pretty_print();

    let new_proof = graph.to_proof();

    return Assertion {
      name,
      is_axiom: false,
      hyps: thm.hyps.clone(),
      disjoint_vars: thm.disjoint_vars.clone(),
      consequent: thm.consequent.clone(),
      proof: new_proof,
    };

    // TODO: should probably make sure that it is maximally simplified.
  }

  // Rendering functions
  
  fn render_sentence(&self, sentence: &Sentence) -> String {
    let mut out = String::new();
    out.push_str(self.consts[sentence.t as usize].name.as_str());
    for word in sentence.words.iter() {

      let name = match word {
        Word::Const(id) => self.consts[*id as usize].name.as_str(),
        Word::Var(id) => self.vars[*id as usize].name.as_str(),
      };

      out.push(' ');
      out.push_str(name);
    }
    return out;
  }

  fn render_decl(&self, decl: &VarDecl) -> String {
    return format!("$f {} {} $.",
      self.consts[decl.t as usize].name, self.vars[decl.var as usize].name);
  }

  fn render_hyp(&self, hyp: &Hypothesis) -> String {
    match hyp {
      Hypothesis::F(decl) => {
        return format!("$f {} {} $.",
          self.consts[decl.t as usize].name, self.vars[decl.var as usize].name);
      },
      Hypothesis::E(ss) => {
        return format!("$e {} $.", self.render_sentence(ss));
      },
    }
  }

  fn num_to_mm_enc(mut num: u32) -> String {
    let mut buf = Vec::<u8>::new();
    buf.push('A' as u8 + (num % 20) as u8);
    num = num / 20;
    while num != 0 {
      num -= 1;
      buf.push('U' as u8 + (num % 5) as u8);
      num /= 5;
    }
    buf.reverse();
    return String::from_utf8(buf).unwrap()
  }

  fn print_assert_statement(&self, assert: &Assertion) {
    // hypotheses
    for (i, hyp) in assert.hyps.iter().enumerate() {
      println!("\t{}.h{} {}", assert.name, i, self.render_hyp(hyp));
    }

    // disjoints
    for (a, b) in assert.disjoint_vars.iter() {
      println!("\t$d {} {} $.", self.vars[*a as usize].name, self.vars[*b as usize].name);
    }
    if assert.is_axiom {
      println!("\t{} $a {} $.", assert.name, self.render_sentence(&assert.consequent));
    } else {
      let hyps_len = assert.hyps.len() as u32;
      // TODO: we could go through the proof and determine which are necessary.
      let mut opt_vars = Vec::<u32>::new();
      let mut var_to_enc = HashMap::<u32, u32>::new();
      let mut assert_to_enc = HashMap::<u32, u32>::new();
      let mut dependencies = vec![];
      for step in assert.proof.iter() {
        match step {
          ProofStep::Var(id) => {
            if var_to_enc.get(id).is_none() {
              var_to_enc.insert(*id, hyps_len + dependencies.len() as u32);
              dependencies.push(step);
              opt_vars.push(*id);
            }
          },
          ProofStep::Assert(id) => {
            if assert_to_enc.get(id).is_none() {
              assert_to_enc.insert(*id, hyps_len + dependencies.len() as u32);
              dependencies.push(step);
            }
          },
          _ => continue,
        }
      }
      let deps_len = dependencies.len() as u32;

      // optional variables
      println!("\t$( optional variables $)");
      for step in dependencies.iter() {
        match step {
          ProofStep::Var(id) => {
            let var = &self.vars[*id as usize];
            println!("\t{}.opt.{} $f {} {} $.",
              assert.name, self.vars[*id as usize].name, 
              self.consts[var.t as usize].name,
              var.name);
          },
          _ => continue,
        }
      }

      println!("\n\t$( optional disjoint statements $)");
      // disjoint statements for optional variables
      if opt_vars.len() > 0 {
        // all optional variables are distinct from each other.
        if opt_vars.len() > 1 {
          print!("\t$d");
          for var in opt_vars.iter() {
            print!(" {}", self.vars[*var as usize].name);
          }
          println!(" $.");
        }
        // all optional variables are distinct from each mandatory variable
        let mand_vars = assert.get_mand_var_set();
        for mand_var in mand_vars.iter() {
          print!("\t$d {}", self.vars[*mand_var as usize].name);
          for var in opt_vars.iter() {
            print!(" {}", self.vars[*var as usize].name);
          }
          println!(" $.");
        }
      }
      println!("");

      println!("\t{} $p {} $.", assert.name, self.render_sentence(&assert.consequent));
    }
  }

  fn print_assert(&self, assert: &Assertion) {
    println!("${{");

    // hypotheses
    for (i, hyp) in assert.hyps.iter().enumerate() {
      println!("\t{}.h{} {}", assert.name, i, self.render_hyp(hyp));
    }

    // disjoints
    for (a, b) in assert.disjoint_vars.iter() {
      println!("\t$d {} {} $.", self.vars[*a as usize].name, self.vars[*b as usize].name);
    }

    if assert.is_axiom {
      println!("\t{} $a {} $.", assert.name, self.render_sentence(&assert.consequent));
    } else {
      let hyps_len = assert.hyps.len() as u32;
      // TODO: we could go through the proof and determine which are necessary.
      let mut opt_vars = Vec::<u32>::new();
      let mut var_to_enc = HashMap::<u32, u32>::new();
      let mut assert_to_enc = HashMap::<u32, u32>::new();
      let mut dependencies = vec![];
      for step in assert.proof.iter() {
        match step {
          ProofStep::Var(id) => {
            if var_to_enc.get(id).is_none() {
              var_to_enc.insert(*id, hyps_len + dependencies.len() as u32);
              dependencies.push(step);
              opt_vars.push(*id);
            }
          },
          ProofStep::Assert(id) => {
            if assert_to_enc.get(id).is_none() {
              assert_to_enc.insert(*id, hyps_len + dependencies.len() as u32);
              dependencies.push(step);
            }
          },
          _ => continue,
        }
      }
      let deps_len = dependencies.len() as u32;

      // optional variables
      println!("\t$( optional variables $)");
      for step in dependencies.iter() {
        match step {
          ProofStep::Var(id) => {
            let var = &self.vars[*id as usize];
            println!("\t{}.opt.{} $f {} {} $.",
              assert.name, self.vars[*id as usize].name, 
              self.consts[var.t as usize].name,
              var.name);
          },
          _ => continue,
        }
      }

      println!("\n\t$( optional disjoint statements $)");
      // disjoint statements for optional variables
      if opt_vars.len() > 0 {
        // all optional variables are distinct from each other.
        if opt_vars.len() > 1 {
          print!("\t$d");
          for var in opt_vars.iter() {
            print!(" {}", self.vars[*var as usize].name);
          }
          println!(" $.");
        }
        // all optional variables are distinct from each mandatory variable
        let mand_vars = assert.get_mand_var_set();
        for mand_var in mand_vars.iter() {
          print!("\t$d {}", self.vars[*mand_var as usize].name);
          for var in opt_vars.iter() {
            print!(" {}", self.vars[*var as usize].name);
          }
          println!(" $.");
        }
      }
      println!("");


      println!("\t{} $p {} $=", assert.name, self.render_sentence(&assert.consequent));

      // depends
      print!("\t(");
      for (i, d) in dependencies.iter().enumerate() {
        match d {
          ProofStep::Var(id) => {
            print!(" {}.opt.{}", assert.name, self.vars[*id as usize].name);
          },
          ProofStep::Assert(id) => {
            print!(" {}", self.asserts[*id as usize].name);
          },
          _ => panic!("invalid"),
        }
      }
      println!(" )");

      // Perform 'compression' for Metamath format.
      // Only dependency statements that are referenced later
      // should get a Z, and then reference numbers need to be renumbered
      // to not include the unused intermediates.
      // NOTE: not doing this resulted in weird failures to verify previously
      // that I don't entirely understand.
      let mut depended_on = vec![false; assert.proof.len()];
      for step in assert.proof.iter() {
        match step {
          ProofStep::Saved(step_id) => {
            match assert.proof[*step_id as usize] {
              ProofStep::Assert(_) => depended_on[*step_id as usize] = true,
              _ => {},
            }
          },
          _ => {},
        }
      }
      let mut saved_id_to_num = Vec::<u32>::new();
      let mut dep_cnt = 0;
      for dep in depended_on.iter() {
        if *dep {
          saved_id_to_num.push(hyps_len + deps_len + dep_cnt);
          dep_cnt += 1;
        } else {
          saved_id_to_num.push(0);
        }
      }
      // println!("$( depended_on: {:?} $)", depended_on);

      // print proof itself
      for (i, step) in assert.proof.iter().enumerate() {
        match step {
          ProofStep::Hyp(id) => {
            print!("{}", MmDb::num_to_mm_enc(*id));
            // print!(" $( hyp $)");
          },
          ProofStep::Var(id) => {
            print!("{}", MmDb::num_to_mm_enc(var_to_enc[id]));
            // print!(" $( var $)");
          },
          ProofStep::Assert(id) => {
            print!("{}", MmDb::num_to_mm_enc(assert_to_enc[id]));
            if depended_on[i] {
              print!("Z");
            }
            // print!(" $( assert $)");
          },
          ProofStep::Saved(step) => {
            match assert.proof[*step as usize] {
              ProofStep::Hyp(id) => {
                print!("{}", MmDb::num_to_mm_enc(id));
                // print!(" $( saved hyp $)");
              },
              ProofStep::Var(id) => {
                print!("{}", MmDb::num_to_mm_enc(var_to_enc[&id]));
                // print!(" $( saved var $)");
              },
              ProofStep::Assert(_) => {
                print!("{}", MmDb::num_to_mm_enc(saved_id_to_num[*step as usize]));
                // print!(" $( saved assert (step: {}) $)", step);
              },
              ProofStep::Saved(step) => panic!("invalid"),
            }
          },
        }
        // println!(" $( {:?} $)", step);
      }

      println!(" $.");
    }
    println!("$}}");
  }

  pub fn print_mm(&self) {
    println!("$( constants $)");
    for c in self.consts.iter() {
      println!("\t$c {} $.", c.name);
    }
    println!("$( variables $)");
    for v in self.vars.iter() {
      println!("\t$v {} $.", v.name);
    }
    for assert in self.asserts.iter() {
      self.print_assert(assert);
    }
  }

  fn get_assert_types(&self) {
    let mut types = HashSet::<u32>::new();
    for assert in self.asserts.iter() {
      types.insert(assert.consequent.t);
    }
    for id in types.iter() {
      println!("{} ({})", self.consts[*id as usize].name, id);
    }
  }

  /**used to test that the ProofGraph from_theorem and to_theorem work
   */
  pub fn test_proof_graph(&self) {
    for assert in self.asserts.iter() {
      if !assert.is_axiom {
        let mut graph = ProofGraph::from_theorem(self, assert);
        let proof = graph.to_proof();
        let theorem = Assertion {
          name: assert.name.clone(),
          is_axiom: false, hyps: assert.hyps.clone(),
          disjoint_vars: assert.disjoint_vars.clone(),
          consequent: assert.consequent.clone(),
          proof: proof
        };
        self.check_proof_validity(&theorem);
      }
    }
  }

  pub fn print_with_all_deps(&self, assert_name: &str) {
    // get all dependencies
    let mut to_visit = HashSet::<u32>::new();
    for (i, assert) in self.asserts.iter().enumerate() {
      if assert.name == assert_name {
        to_visit.insert(i as u32);
        break;
      }
    }
    let mut visited = HashSet::<u32>::new();
    while to_visit.len() != 0 {
      let mut to_visit_l: Vec<u32> = to_visit.drain().collect();
      for assert_id in to_visit_l.drain(0..) {
        if !visited.contains(&assert_id) {
          for step in self.asserts[assert_id as usize].proof.iter() {
            if let ProofStep::Assert(id) = step {
              to_visit.insert(*id);
            }
          }
          visited.insert(assert_id);
        }
      }
    }

    let mut deps: Vec<u32> = visited.drain().collect();
    deps.sort();

    // print
    println!("$( constants $)");
    for c in self.consts.iter() {
      println!("\t$c {} $.", c.name);
    }
    println!("$( variables $)");
    for v in self.vars.iter() {
      println!("\t$v {} $.", v.name);
    }
    for assert_id in deps.iter() {
      self.print_assert(&self.asserts[*assert_id as usize]);
    }
  }

  /**used to test that the ProofGraph from_theorem and to_theorem work
   */
  pub fn test_unfold(&self) {
    for assert in self.asserts.iter() {
      if !assert.is_axiom {
        let mut thm_deps = HashSet::<u32>::new();
        for step in assert.proof.iter() {
          match step {
            ProofStep::Assert(id) => {
              if !self.asserts[*id as usize].is_axiom {
                thm_deps.insert(*id);
              }
            },
            _ => continue,
          }
        }
        for dep_id in thm_deps.iter() {
          let to_unfold = &self.asserts[*dep_id as usize];
          // println!("$(");
          // println!("assert disjoint_vars:");
          // for (a, b) in assert.disjoint_vars.iter() {
          //   println!("\t({}, {})", a, b);
          // }
          let unfolded = self.unfold(
            format!("{}.unfold.{}", assert.name, to_unfold.name),
            assert, *dep_id);
          // println!();
          // println!("unfolded disjoint_vars.len() = {}", unfolded.disjoint_vars.len());
          // for (a, b) in unfolded.disjoint_vars.iter() {
          //   println!("\t({}, {})", a, b);
          // }
          // println!();
          // println!("proof:");
          // for step in unfolded.proof.iter() {
          //   println!("\t{:?}", step);
          // }
          // println!("$)");
          // self.print_assert(&assert);
          // println!("$( ----------------------- $)");
          self.print_assert(&unfolded);
          // println!("$( ----------------------- $)");
          // println!("$( {}.proof.len() = {} $)", unfolded.name, unfolded.proof.len());
          // println!("$( checking proof:");
          self.check_proof_validity(&unfolded);
          // println!("$)");
          // self.add_theorem(unfolded.name, unfolded.hyps, unfolded.consequent, unfolded.disjoint_vars, unfolded.deps, unfolded.proof);
        }
      }
    }
  }
}
