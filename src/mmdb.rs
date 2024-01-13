use std::collections::{ HashMap, HashSet, VecDeque };
use std::fmt::format;
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
#[derive(Clone, Debug)]
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
  fn get_all_var_set(&self, mmdb: &MmDb) -> HashSet<u32> {
    let mut var_set = HashSet::<u32>::new();
    for hyp in self.hyps.iter() {
      match hyp {
        Hypothesis::F(decl) => { var_set.insert(decl.var); },
        _ => {},
      }
    }

    for sym in self.deps.iter() {
      match sym.t {
        SymbolType::Hyp => {
          match mmdb.hyps[sym.id as usize] {
            Hypothesis::F(decl) => { var_set.insert(decl.var); },
            _ => continue,
          }
        }
        _ => continue,
      }
    }

    return var_set;
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
  step: ProofStep,
}

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
    for step in theorem.proof.iter() {
      match step {
        ProofStep::Hyp(id) => {
          let node_id = graph.add_node(ProofNode { step: step.clone() });
          stack.push(node_id);
          steps.push(node_id);
        },
        ProofStep::Dep(id) => {
          let sym = &theorem.deps[*id as usize];
          match sym.t {
            SymbolType::Hyp => {
              let node_id = graph.add_node(ProofNode { step: step.clone() });
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
                ProofNode { step: step.clone() },
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
        ProofStep::Dep(id) => {
          let sym = &theorem.deps[*id as usize];
          match sym.t {
            SymbolType::Hyp => {
              let node_id = self.add_node(ProofNode { step: step.clone() });
              stack.push(node_id);
              steps.push(node_id);
            },
            SymbolType::Assert => {
              let assert = &mmdb.asserts[sym.id as usize];
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
          // let step = &self.nodes[child_id].step;
          // match step {
          //   ProofStep::Hyp(_) => {
          //     proof.push(step.clone());
          //   },
          //   ProofStep::Dep(_) => {
          //     proof.push(ProofStep::Saved(node_to_step[child_id]));
          //   },
          //   _ => panic!("invalid"),
          // }
        }
      } else {
        visited[node] = true;
        node_to_step[node] = proof.len() as u32;
        match self.nodes[node].step {
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

  fn permute_all_variables(&self, assert: &mut Assertion) {
    fn remap_ss(ss: &mut SymStr, &var_var_map: Vec<u32>) {
      for sym in ss.syms.iter_mut() {
        match sym.t {
          SymbolType::Var => {
            sym.id = var_var_map[sym.id as usize];
          },
          _ => continue,
        }
      }
    }

    // create a map that maps old variables to new variables
    // first, collect variables by type
    let mut type_to_vars = HashMap::<u32, Vec<u32>>::new();
    for (var_id, var) in self.vars.iter().enumerate() {
      if !var.type_declared {
        panic!("invalid");
      }
      match type_to_vars.get_mut(var.t) {
        Some(vars) => {
          vars.push(var_id);
        },
        None => {
          type_to_vars.insert(var.t, vec![var_id]);
        }
      }
    }

    // then permute these, within their type
    let mut rng = rand::thread_rng();
    for (_, vars) in type_to_vars.iter_mut() {
      vars.shuffle(&mut rng);
    }

    // then create a map for variable ids to variable ids
    let mut var_var_map = vec![];
    for (var_id, var) in self.vars.iter().enumerate() {
      let remapped_to = type_to_vars.get_mut(var.t).pop().unwrap();
      var_var_map.push(remapped_to);
    }

    // create a map that maps variables to hypotheses
    // TODO: this is pretty annoying, and we should just use variables
    // instead of hypotheses at some point.
    let mut var_hyp_map = vec![0; self.vars.len()];
    for (hyp_id, hyp) in self.hyps.iter().enumerate() {
      match hyp {
        Hypothesis::F(decl) => var_hyp_map[decl.id] = hyp_id,
        _ => {},
      }
    }

    // permute vars in deps
    for sym in assert.deps.iter_mut() {
      match sym.t {
        SymbolType::Hyp => {
          let var_id = self.hyps[sym.id as usize];
          match self.hyps[sym.id as usize] {
            Hypothesis::F(decl) => {
              sym.id = var_hyp_map[decl.var];
            },
            _ => panic!("invalid"),
          }
        },
        _ => continue,
      }
    }

    // permute vars in hyps
    for hyp in assert.hyps.iter_mut() {
      match hyp {
        Hypothesis::F(decl) => { decl.var = var_var_map[decl.var as usize]; },
        Hypothesis::E(ss)   => { remap_ss(ss, &var_var_map); },
      }
    }

    // permute vars in disjoints
    for (a, b) in assert.disjoint_vars.iter_mut() {
      a = var_var_map[a as usize];
      b = var_var_map[b as usize];
    }

    // permute vars in  consequent
    remap_ss(&mut assert.consequent, &var_var_map);
  }

  /**Go through all optional variables of assertion, and if they are
   * in the excluded vars set, then change them to some different
   * variable.
   */
  fn change_optional_variables(&self,
    thm: &mut Assertion,
    excluded_vars: &HashSet<u32>)
  {
    for sym in new_deps.iter() {
      match sym.t {
        SymbolType::Hyp => {
          match self.hyps[sym.id] {
            Hypothesis::F(decl) => {
              if mand_vars.contains(decl.var) {
                // uh oh, we need to fix this!
                
              }
            },
            _ => panic!("invalid"),
          }
        },
        _ => continue,
      }
    }
  }


  /**Unfolding a dependency in an assertion will remove all references
   * to that dependency in the proof and will replace them with an inlined
   * proof of the dependency.
   */
  fn unfold(&self, name: String, thm: &Assertion, dep_id: u32) -> Assertion {
    if thm.is_axiom {
      panic!("invalid");
    }
    let to_unfold_sym = &thm.deps[dep_id as usize];

    if to_unfold_sym.t != SymbolType::Assert
    || self.asserts[to_unfold_sym.id as usize].is_axiom {
      // cannot unfold a hypothesis (which must be a floating hypothesis)
      // cannot unfold an axiom
      // alternately: unfolding an axiom is a trivial operation
      let mut out = thm.clone();
      out.name = name;
      return out;
    }

    // sanity check -- does the theorem contain the dependency?
    let mut contains_dep = false;
    for step in thm.proof.iter() {
      match step {
        ProofStep::Dep(id) => {
          if *id == dep_id {
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

    // first, remap the dependencies
    let mut to_unfold = self.asserts[to_unfold_sym.id as usize].clone();

    let all_vars = thm.get_all_var_set(self);
    // TODO: technically, we could see all the variables that are substituted,
    // and then check the disjoint conditions, and then re-use local variables
    // if needed, but that is lot of work.
    self.change_optional_variables(&mut to_unfold, all_vars);

    let mut to_unfold_dep_map = Vec::<u32>::new();
    let mut new_deps = thm.deps.clone();
    // TODO: O(n^2), could be asymptotically improved
    for dep in to_unfold.deps.iter() {
      let mut dep_ind = new_deps.len();
      for (i, dep0) in new_deps.iter().enumerate() {
        if *dep == *dep0 {
          dep_ind = i;
          break;
        }
      }
      if dep_ind >= new_deps.len() {
        // push new dependency
        new_deps.push(dep.clone());
        
      }
      to_unfold_dep_map.push(dep_ind as u32);
    }
    to_unfold.deps = new_deps;
    for step in to_unfold.proof.iter_mut() {
      match step {
        ProofStep::Dep(id) => {
          *id = to_unfold_dep_map[*id as usize];
        },
        _ => {},
      }
    }
    // TODO: fix deps.
    // go through and get all optional vars
    // need to get the set of optional variables in the dependencies.
    // then union the set of optional variables.
    // then remap the optional variables.

    let mut graph = ProofGraph::from_theorem(self, &thm);
    println!("graph before:");
    graph.pretty_print();
    let mut nodes_to_unfold = vec![];
    for (node_id, node) in graph.nodes.iter().enumerate() {
      if let ProofStep::Dep(id) = node.step {
        if id == dep_id {
          nodes_to_unfold.push(node_id);
        }
      }
    }
    for node_id in nodes_to_unfold.iter() {
      graph.unfold_theorem(*node_id, self, &to_unfold);
    }
    println!("graph after:");
    graph.pretty_print();

    // the dependency is now removed -- we can now remap all dependencies so that
    // the dependency is removed.
    to_unfold.deps.remove(dep_id as usize);
    let mut new_proof = graph.to_proof();
    for step in new_proof.iter_mut() {
      if let ProofStep::Dep(id) = step {
        if *id > dep_id {
          *id -= 1;
        }
      }
    }
    return Assertion {
      name,
      is_axiom: false,
      hyps: thm.hyps.clone(),
      disjoint_vars: thm.disjoint_vars.clone(),
      consequent: thm.consequent.clone(),
      deps: to_unfold.deps,
      proof: new_proof,
    };

    // TODO: should probably make sure that it is maximally simplified.
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
    println!("$( assert.disjoint_vars.len() = {} $)", assert.disjoint_vars.len());
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
            if depended_on[i] {
              print!("Z");
            }
          },
          ProofStep::Saved(step) => {
            match assert.proof[*step as usize] {
              ProofStep::Hyp(id) => {
                print!("{}", MmDb::num_to_mm_enc(id));
              },
              ProofStep::Dep(_) => {
                print!("{}", MmDb::num_to_mm_enc(saved_id_to_num[*step as usize]));
              },
              ProofStep::Saved(step) => panic!("invalid"),
            }
          },
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

  /**used to test that the ProofGraph from_theorem and to_theorem work
   */
  pub fn test_unfold(&self) {
    for assert in self.asserts.iter() {
      if !assert.is_axiom {
        for (dep_id, dep) in assert.deps.iter().enumerate() {
          if dep.t == SymbolType::Assert {
            let to_unfold = &self.asserts[dep.id as usize];
            if !to_unfold.is_axiom {
              println!("$(");
              println!("assert disjoint_vars:");
              for (a, b) in assert.disjoint_vars.iter() {
                println!("\t({}, {})", a, b);
              }
              let unfolded = self.unfold(
                format!("{}.unfold.{}", assert.name, to_unfold.name),
                assert, dep_id as u32);
              println!();
              println!("unfolded disjoint_vars.len() = {}", unfolded.disjoint_vars.len());
              for (a, b) in unfolded.disjoint_vars.iter() {
                println!("\t({}, {})", a, b);
              }
              println!();
              println!("proof:");
              for step in unfolded.proof.iter() {
                println!("\t{:?}", step);
              }
              println!("$)");
              // self.print_assert(&assert);
              // println!("$( ----------------------- $)");
              self.print_assert(&unfolded);
              println!("$( ----------------------- $)");
              self.check_proof_validity(&unfolded);
              // self.add_theorem(unfolded.name, unfolded.hyps, unfolded.consequent, unfolded.disjoint_vars, unfolded.deps, unfolded.proof);
            }
          }
        }
      }
    }
  }
}
