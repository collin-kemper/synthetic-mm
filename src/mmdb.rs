use std::collections::{ HashMap, HashSet, VecDeque };
use std::io::prelude::*;

use rand::prelude::*;

#[derive(PartialEq, Eq, Clone)]
pub enum SymbolType {
  Var,
  Const,
  Hyp,
  Assert,
}

#[derive(PartialEq, Eq, Clone)]
pub struct Symbol {
  pub t: SymbolType,
  pub id: u32,
}

#[derive(Clone)]
pub struct SymStr {
  pub t: u32,
  pub syms: Vec<Symbol>,
}

impl SymStr {
  pub fn new(t: u32) -> SymStr {
    return SymStr {
      t: t,
      syms: Vec::new(),
    };
  }
}

#[derive(Clone)]
pub struct VarDecl {
  pub t: u32,
  pub var: u32,
}

#[derive(Clone)]
pub enum Hypothesis {
  F(VarDecl),
  E(SymStr),
}

impl Hypothesis {
  fn to_ss(&self) -> SymStr {
    match self {
      Hypothesis::F(decl) =>
        SymStr {
          t: decl.t,
          syms: vec![
            Symbol { t: SymbolType::Var, id: decl.var }
          ]
        },
      Hypothesis::E(ss) => ss.clone(),
    }
  }
}

// Proof
// a proof is a series of steps.
// each step is either saved or not.
// steps can reference a hypothesis, a dependency, or a saved step
// 
#[derive(Clone)]
pub enum ProofStep {
  Hyp(u32),
  Dep(u32),
  Saved(u32),
}

#[derive(Clone)]
struct Assertion {
  name: String,
  is_axiom: bool,

  // The assertions that the proof of this assertion depends on.
  hyps: Vec<Hypothesis>,
  disjoint_vars: Vec<(u32, u32)>,
  consequent: SymStr,

  deps: Vec<Symbol>,
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
}

struct Var {
  name: String,
  type_declared: bool,
  t: u32,
}

struct Const {
  name: String,
}

struct ProofNode {
  data: ProofStep,
}

struct ProofGraph {
  nodes: Vec<ProofNode>,
  root: usize,
  edges: Vec<Vec<usize>>,
}

impl ProofGraph {
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
    for step in theorem.proof.iter() {
      match step {
        ProofStep::Hyp(id) => {
          let node_id = graph.add_node(ProofNode { data: step.clone() });
          stack.push(node_id);
          steps.push(node_id);
        },
        ProofStep::Dep(id) => {
          let sym = &theorem.deps[*id as usize];
          match sym.t {
            SymbolType::Hyp => {
              let node_id = graph.add_node(ProofNode { data: step.clone() });
              stack.push(node_id);
              steps.push(node_id);
            },
            SymbolType::Assert => {
              let assert = &mmdb.asserts[sym.id as usize];
              if assert.hyps.len() > stack.len() {
                panic!("invalid");
              }
              let hyps_start = stack.len() - assert.hyps.len();
              let node_id = graph.add_node_with_edges(
                ProofNode { data: step.clone() },
                &stack[hyps_start..]
              );
              stack.truncate(hyps_start);
              stack.push(node_id);
              steps.push(node_id);
            },
            _ => panic!("invalid"),
          }
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
        match self.nodes[node].data {
          ProofStep::Hyp(id) => proof.push(ProofStep::Hyp(id)),
          ProofStep::Dep(id) => proof.push(ProofStep::Dep(id)),
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
  pub hyps: Vec<Hypothesis>,
  pub asserts: Vec<Assertion>,
}

impl MmDb {
  pub fn new() -> MmDb {
    return MmDb {
      vars: Vec::new(),
      consts: Vec::new(),
      hyps: Vec::new(),
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

  pub fn add_variable(&mut self, name: String) -> u32 {
    let id = self.vars.len() as u32;
    self.vars.push(Var { name: name, type_declared: false, t: 0 });
    return id;
  }

  pub fn add_floating(&mut self, t: u32, var: u32) -> u32 {
    // We impose an additional constraint that variables never have different
    // types in different scopes. Really, variable declarations should be the same
    // as floating declarations, as there is no context in which you can use a variable
    // without a type.
    if self.vars[var as usize].type_declared {
      if self.vars[var as usize].t != t {
        panic!("invalid");
      }
    } else {
      self.vars[var as usize].type_declared = true;
      self.vars[var as usize].t = t;
    }

    let id = self.hyps.len();
    self.hyps.push(Hypothesis::F(VarDecl { t, var }));
    return id as u32;
  }

  pub fn add_essential(&mut self, t: u32, syms: Vec<Symbol>) -> u32 {
    let id = self.hyps.len();
    self.hyps.push(Hypothesis::E(SymStr { t, syms }));
    return id as u32;
  }

  pub fn add_axiom(&mut self,
    name: String,
    hyps: Vec<Hypothesis>,
    consequent: SymStr,
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
      deps: vec![],
      proof: vec![],
    });

    return assert_id;
  }

  pub fn add_theorem(&mut self,
    name: String,
    hyps: Vec<Hypothesis>,
    consequent: SymStr,
    disjoint_vars: Vec<(u32, u32)>,
    deps: Vec<Symbol>,
    proof: Vec<ProofStep>)
    -> u32
  {
    

    let theorem = Assertion {
      name: name,
      is_axiom: false,
      hyps: hyps,
      consequent: consequent,
      disjoint_vars: disjoint_vars,
      deps,
      proof: proof,
    };

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
  fn apply(stack: &mut Vec<SymStr>, assert: &Assertion,
    mand_vars: &HashSet<u32>,
    disjoint_vars: &HashSet<(u32, u32)>)
  {
    // check to ensure that there are enough statements on the stack to apply assert
    if stack.len() < assert.hyps.len() {
      panic!("invalid");
    }

    // construct variable map and check that the stack matches assert's
    // hypotheses
    let mut var_map: HashMap<u32, Vec<Symbol>> = HashMap::new();
    let hyp_start = stack.len() - assert.hyps.len();
    for i in 0..assert.hyps.len() {
      let stack_entry = &stack[hyp_start + i];
      match &assert.hyps[i] {
        Hypothesis::F(decl) => {
          if stack_entry.t != decl.t {
            panic!("invalid");
          }
          var_map.insert(decl.var, stack_entry.syms.clone());
        },
        Hypothesis::E (ss)     => {
          if stack_entry.t != ss.t {
            panic!("invalid");
          }

          // TODO: unnecessary allocation?
          let mut ss_sub = Vec::<Symbol>::new();
          for sym in ss.syms.iter() {
            if sym.t == SymbolType::Var {
              let sub = var_map.get(&sym.id).unwrap();
              ss_sub.extend_from_slice(sub.as_slice());
            } else {
              ss_sub.push(sym.clone());
            }
          }

          if ss_sub.len() != stack_entry.syms.len() {
            panic!("invalid");
          }
          for i in 0..ss_sub.len() {
            if ss_sub[i] != stack_entry.syms[i] {
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
    for (v, syms) in var_map.iter() {
      if !mand_vars.contains(v) {
        continue;
      }
      for s in syms {
        if s.t == SymbolType::Var {
          if !mand_vars.contains(&s.id) {
            continue;
          }
          var_set.insert(s.id);
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
    for (a, b) in &assert.disjoint_vars {
      if !mand_vars.contains(a) || !mand_vars.contains(b) {
        continue;
      }
      for s0 in var_var_map.get(a).unwrap() {
        for s1 in var_var_map.get(b).unwrap() {
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
    let mut consequent = SymStr { t: assert.consequent.t, syms: Vec::new() };
    for sym in &assert.consequent.syms {
      if sym.t == SymbolType::Var {
        consequent.syms.extend_from_slice(var_map.get(&sym.id).unwrap().as_slice());
      } else {
        consequent.syms.push(sym.clone());
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

    let mut stack = Vec::<SymStr>::new();
    let mut saved_statements = Vec::<SymStr>::new();
    let mand_vars = theorem.get_mand_var_set();

    let mut i = 0;
    for step in theorem.proof.iter() {
      match step {
        ProofStep::Hyp(id) => {
          let hyp = &theorem.hyps[*id as usize];
          stack.push(hyp.to_ss());
        },
        ProofStep::Dep(id) => {
          let sym = &theorem.deps[*id as usize];
          match sym.t {
            SymbolType::Hyp => {
              let hyp = &self.hyps[sym.id as usize];
              stack.push(hyp.to_ss());
            },
            SymbolType::Assert => {
              let assert = &self.asserts[sym.id as usize];
              MmDb::apply(&mut stack, assert, &mand_vars, &disjoint_var_set);
            },
            _ => panic!("invalid"),
          }
        },
        ProofStep::Saved(id) => {
          let st = saved_statements[*id as usize].clone();
          stack.push(st);
        },
      }
      saved_statements.push(stack[stack.len()-1].clone());
    }

    // check that top of stack matches consequent
    if stack.len() != 1 {
      panic!("invalid");
    }
    // check that top of stack is same as assertion, then create assertion
    if theorem.consequent.syms.len() != stack[0].syms.len() {
      panic!("invalid");
    }
    if theorem.consequent.t != stack[0].t {
      panic!("invalid");
    }
    for i in 0..theorem.consequent.syms.len() {
      if theorem.consequent.syms[i] != stack[0].syms[i] {
        panic!("invalid");
      }
    }
    return;
  }


  /**Unfolding a dependency in an assertion will remove all references
   * to that dependency in the proof and will replace them with an inlined
   * proof of the dependency.
   */
  fn unfold(&self, name: String, thm: &Assertion, dep_id: u32) -> Assertion {
    panic!("unimplemented");
    // if thm.is_axiom {
    //   panic!("invalid");
    // }
    // let to_unfold_sym = thm.deps[dep_id as usize];

    // if to_unfold_sym.t != SymbolType:Assert
    // || self.asserts[to_unfold_sym.id as usize].is_axiom {
    //   // cannot unfold a hypothesis (which must be a floating hypothesis)
    //   // cannot unfold an axiom
    //   // alternately: unfolding an axiom is a trivial operation
    //   let out = thm.clone();
    //   out.name = name;
    //   return out;
    // }

    // // sanity check
    // let mut contains_dep = false;
    // for sep in thm.proof.iter() {
    //   match step {
    //     ProofStep::Dep(id) => {
    //       if *id == dep_id {
    //         contains_dep = true;
    //         break;
    //       }
    //     },
    //     _ => continue,
    //   }
    // }
    // if !contains_dep {
    //   panic!("invalid");
    // }

    // let to_unfold = &self.asserts[to_unfold_sym.id as usize];

    // // create new dep vector that excludes the dependency we are unfolding.
    // let mut deps = Vec::<Symbol>::with_capacity(thm.deps.len());
    // deps.extend_from_slice(&thm.deps[0..(dep_id as usize)]);
    // deps.extend_from_slice(&thm.deps[(dep_id as usize + 1)..]);

    // // this maps the dependency id in to_unfold to its new dependency
    // // id in the new assertion.
    // let mut to_unfold_dep_map = Vec::<u32>::new();

    // for dep in to_unfold.deps.iter() {
    //   //  todo: add new deps
    //   let mut already_contains = false;
    //   let mut dep_ind = deps.len();
    //   for (i, dep0) in deps.iter().enumerate() {
    //     if *dep == *dep0 {
    //       dep_ind = i;
    //       break;
    //     }
    //   }
    //   if dep_ind >= deps.len() {
    //     // push new dependency
    //     deps.push(dep.clone());
        
    //   }
    //   to_unfold_dep_map.push(dep_ind);
    // }


    // // whenever we push a hypothesis of to_unfold, we must replace this with
    // // the constructed hypothesis in thm....
    // // otherwise, everything else can be the same (module remapping ids).
    // // 
    // let mut stack = Vec::<(ProofStep, u32, u32)>::new()
    // // let mut saved_statements = Vec::<SymStr>::new();
    // let mut saved_statement_cnt = 0;

    // let mut proof = Vec::<ProofStep>::new();
    // // maps old saved id to new saved id
    // let mut saved_map = Vec::<u32>::new();
    // for step in thm.proof.iter() {
    //   match step {
    //     ProofStep::Hyp(id) => {
    //       proof.push(step.clone());
    //       stack.push(step.clone());
    //     },
    //     ProofStep::Dep(id) => {
    //       let sym = &theorem.deps[*id as usize];
    //       match sym.t {
    //         SymbolType::Hyp => {
    //           if *id > dep_id {
    //             proof.push(ProofStep::Dep(*id - 1));
    //             stack.push(ProofStep::Dep(*id - 1));
    //           } else {
    //             proof.push(ProofStep::Dep(*id));
    //             stack.push(ProofStep::Dep(*id));
    //           }
    //           // let hyp = &self.hyps[sym.id as usize];
    //           // stack.push(hyp.to_ss());
    //         },
    //         SymbolType::Assert => {
    //           let assert = &self.asserts[sym.id as usize];
    //           if *id < dep_id {
    //             if assert.hyps.len() > stack.len() {
    //               panic!("invalid");
    //             }
    //             let new_stack_sz = stack.len() - assert.hyps.len();
    //             stack.truncate(new_stack_sz);
    //             proof.push(step.clone());
    //             stack.push(step.clone());
    //             // we will be adding a bunch of saved statements, so 
    //             // we need to remap the ids of these
    //             saved_map.push(saved_statement_cnt);
    //             saved_statement_cnt += 1;
    //           } else if *id == dep_id {
    //             /* unfold the to_unfold dependency */

    //             // first, get the replacements for the hypotheses of the dependency
    //             let mut hyp_replacements = Vec::<ProofStep>::new();
    //             let hyp_start = stack.len() - assert.hyps.len();
    //             for i in 0..assert.hyps.len() {
    //               match stack[hyp_start + i] {
    //                 ProofStep::Hyp(id) => {
    //                   // hypotheses replace hypotheses
    //                   hyp_replacements.push(ProofStep::Hyp(id));
    //                 },
    //                 ProofStep::Dep(id) => {
    //                   // references to the dependency replace dependencies
    //                   hyp_replacements.push(ProofStep::Saved(TODO));
    //                 },
    //                 ProofStep::Saved(id) => {
    //                   // saved statements replace saved statements
    //                   hyp_replacements.push(ProofStep::Saved(id));
    //                 },
    //               }
    //             }

    //             let saved_offset = saved_statement_cnt;
    //             for step in assert.proof.iter() {
    //               match step {
    //                 ProofStep::Hyp(id) => {
    //                   proof.push(hyp_replacements[*id as usize]);
    //                   stack.push(hyp_replacements[*id as usize])
    //                 },
    //                 ProofStep::Dep(id) => {
    //                   let sym = &theorem.deps[*id as usize];
    //                   match sym.t {
    //                     SymbolType::Hyp => {
    //                       // TODO
    //                     },
    //                     SymbolTYpe::Assert => {
    //                       // TODO?
    //                       let assert = &self.asserts[sym.id as usize];
    //                       if assert.hyps.len() > stack.len() {
    //                         panic!("invalid");
    //                       }
    //                       let new_stack_sz = stack.len() - assert.hyps.len();
    //                       stack.truncate(new_stack_sz);
    //                       proof.push(
    //                         ProofStep::Dep(to_unfold_dep_map[*id as usize]));
    //                       stack.push(
    //                         ProofStep::Dep(to_unfold_dep_map[*id as usize]));
    //                       saved_statement_cnt += 1;
    //                     },
    //                     _ => panic!(),
    //                   }
    //                 },
    //                 ProofStep::Saved(id) => {
    //                   proof.push(ProofStep::Saved(saved_offset + id));
    //                   stack.push(ProofStep::Saved(saved_offset + id));
    //                 },
    //               }
    //             }
                
    //           } else { /* *id > dep_id */
    //             if assert.hyps.len() > stack.len() {
    //               panic!("invalid");
    //             }
    //             let new_stack_sz = stack.len() - assert.hyps.len();
    //             stack.truncate(new_stack_sz);
    //             proof.push(ProofStep::Dep(*id - 1));
    //             stack.push(ProofStep::Dep(*id - 1));
    //             // we will be adding a bunch of saved statements, so 
    //             // we need to remap the ids of these
    //             saved_map.push(saved_statement_cnt);
    //             saved_statement_cnt += 1;
    //           }
    //           // MmDb::apply(&mut stack, assert, &mand_vars, &disjoint_var_set);
    //           // saved_statements.push(stack[stack.len()-1].clone());
    //         },
    //         _ => panic!("invalid"),
    //       }
    //     },
    //     ProofStep::Saved(id) => {
    //       proof.push(ProofStep::Saved(saved_map[id]));
    //     },
    //   }
    // }

    // // normalize proof.

    // // All references to hypotheses become hypotheses
    // for step in proof.mut_iter() {
    //   if let ProofStep::Saved(id) = &step {
    //     match &proof[id as usize] {
    //       ProofStep::Hyp(_) => step = proof[id].clone(),
    //       ProofStep::Saved(id) => step = proof[id].clone(),
    //       _ => continue,
    //     }
    //   }
    // }

    // // for every non top element of the stack,
    // // replace the first saved reference to it with the proof steps.
    // // Then replace all further saved references to it with references
    // // to it at its new location.
    // if stack.len() > 1 {
    //   let out = whatever;
    //   let mut queue = VecDeque::<node>::new();
    //   queue.push_back(final step in proof);
    //   while let Some(node) = queue.pop_front() {
    //     for child in node {
    //       queue.push_back(child);
    //     }
    //     if 
    //   }
    //   // TODO: remove unused parts of the proof.
    //   let mut step_use_cnt = vec![0, proof.len()];
    //   for (i, step) in proof.iter().enumerate() {
    //     match step with {
    //       ProofStep::Hyp(id) => {},
    //       ProofStep::Dep(id) => {
    //         match deps[id].t {
    //           Symbol::Hyp => {},
    //           Symbol::Assert => {
    //             // the 
    //           },
    //           _ => panic!("invalid"),
    //         }
            
    //       },
    //       ProofStep::Saved(id) => {
    //         step_use_cnd[id] += 1;
    //       },
          
    //     }

    //   }
    //   let step_remap = vec![0, proof.len()];
    //   for (i, step) in proof.iter().enumerate() {
    //     match step with {
    //       ProofStep::Hyp(id) => ,
    //       ProofStep::Dep(id) => {
            
    //       },
    //       ProofStep::Saved(id) => {
    //         if !step_used[*id as usize] {
    //           // saved step referenced before first use!
    //           // go backwards, 


    //           step_remap[id] = cur_step;
    //         }
    //       },
          
    //     }
    //   }
    //   for item in stack[0..stack.len()-1].iter() {
    //     // ensure that it is redundant.
    //   }

    //   // Now, remove all redundant parts of the proof.
    //   let mut reduced_proof = Vec::<ProofStep>::new();
    //   let mut deleted_steps = 0;
    //   for (i, step) in proof.drain().enumerate() {
    //     if step_is_necessary[i] {
    //       match step {
    //         ProofStep::Hyp(id) => reduced_proof.push(step),
    //         ProofStep::Dep(id) => reduced_proof.push(step),
    //         ProofStep::Saved(id) => reduced_proof.push(
    //           ProofStep::Saved(id - deleted_steps)
    //         ),
    //       } 
    //     } else {
    //       deleted_steps += 1;
    //     }
    //   }
    //   proof = new_proof;
    // }


    // let mut step_referenced = vec![false; proof.len()];
    // for step in &

    // return Assertion {
    //   name,
    //   is_axiom: false,
    //   hyps: thm.hyps.clone(),
    //   disjoint_vars: thm.disjoint_vars.clone(),
    //   consequent: thm.consequent.clone(),
    //   deps,
    //   proof,
    // };
  }

  // Rendering functions
  
  fn render_ss(&self, ss: &SymStr) -> String {
    let mut out = String::new();
    out.push_str(self.consts[ss.t as usize].name.as_str());
    for sym in ss.syms.iter() {
      let name = match sym.t {
        SymbolType::Const => {
          self.consts[sym.id as usize].name.as_str()
        },
        SymbolType::Var => {
          self.vars[sym.id as usize].name.as_str()
        },
        _ => panic!("invalid"),
      };
      out.push(' ');
      out.push_str(name);
    }
    return out;
  }

  fn display_asserts(&self) {
    for assert in &self.asserts {
      println!("----------------");
      println!("{}:", assert.name);
      for (i, hyp) in assert.hyps.iter().enumerate() {
        let ss = hyp.to_ss();
        println!("\th{}: {}", i, self.render_ss(&ss));
      }
      println!("\t{}", self.render_ss(&assert.consequent));
    }
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
        return format!("$e {} $.", self.render_ss(ss));
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

  fn print_assert(&self, assert: &Assertion) {
    println!("${{");

    // disjoints
    for (a, b) in assert.disjoint_vars.iter() {
      println!("\t$d {} {} $.", self.vars[*a as usize].name, self.vars[*b as usize].name);
    }
    // TODO: we could go through the proof and determine which are necessary.
    let mut opt_vars = Vec::<u32>::new();
    for dep in assert.deps.iter() {
      if SymbolType::Hyp == dep.t {
        if let Hypothesis::F(decl) = &self.hyps[dep.id as usize] {
          opt_vars.push(decl.var);
        }
      }
    }
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

    // optional hypotheses
    for (i, d) in assert.deps.iter().enumerate() {
      match d.t {
        SymbolType::Hyp => {
          println!("\t{}.opt{} {}", assert.name, i, self.render_hyp(&self.hyps[d.id as usize]));
        },
        _ => continue,
      }
    }

    println!("");

    // hypotheses
    for (i, hyp) in assert.hyps.iter().enumerate() {
      println!("\t{}.h{} {}", assert.name, i, self.render_hyp(hyp));
    }

    if assert.is_axiom {
      println!("\t{} $a {} $.", assert.name, self.render_ss(&assert.consequent));
    } else {
      println!("\t{} $p {} $=", assert.name, self.render_ss(&assert.consequent));

      // depends
      print!("\t(");
      for (i, d) in assert.deps.iter().enumerate() {
        match d.t {
          SymbolType::Hyp => {
            print!(" {}.opt{}", assert.name, i);
          },
          SymbolType::Assert => {
            print!(" {}", self.asserts[d.id as usize].name);
            
          },
          _ => panic!("invalid"),
        }
      }
      println!(" )");

      let hyps_len = assert.hyps.len() as u32;
      let deps_len = assert.deps.len() as u32;

      // Perform 'compression' for Metamath format.
      // Only dependency statements that are referenced later
      // should get a Z, and then reference numbers need to be renumbered
      // to not include the unused intermediates.
      // NOTE: not doing this resulted in weird failures to verify previously
      // that I don't entirely understand.
      let mut depended_on = vec![false; assert.proof.len()];
      for step in assert.proof.iter() {
        match step {
          ProofStep::Saved(id) => {
            depended_on[*id as usize] = true;
          },
          _ => {},
        }
      }
      let mut saved_id_to_num = Vec::<u32>::new();
      let mut dep_cnt = 0;
      for dep in depended_on.iter() {
        if *dep {
          saved_id_to_num.push(dep_cnt + hyps_len + deps_len);
          dep_cnt += 1;
        } else {
          saved_id_to_num.push(0);
        }
      }

      // print proof itself
      for (i, step) in assert.proof.iter().enumerate() {
        match step {
          ProofStep::Hyp(id) => {
            print!("{}", MmDb::num_to_mm_enc(*id));
          },
          ProofStep::Dep(id) => {
            print!("{}", MmDb::num_to_mm_enc(*id + hyps_len));
            if assert.deps[*id as usize].t == SymbolType::Assert {
            }
          },
          ProofStep::Saved(id) => {
            print!("{}", MmDb::num_to_mm_enc(saved_id_to_num[*id as usize]));
          },
        }
        if depended_on[i] {
          print!("Z");
        }
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
          deps: assert.deps.clone(),
          proof: proof
        };
        self.check_proof_validity(&theorem);
      }
    }
  }
}
