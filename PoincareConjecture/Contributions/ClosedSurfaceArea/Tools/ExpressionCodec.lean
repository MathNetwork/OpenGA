import Lean

open Lean Meta

partial def exportNormalize (renames : Std.HashMap Name Name) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n ls => some (.const (renames.getD n n) ls)
    | .mdata _ v => some (exportNormalize renames v)
    | .forallE _ t b i => some (.forallE .anonymous (exportNormalize renames t) (exportNormalize renames b) i)
    | .lam _ t b i => some (.lam .anonymous (exportNormalize renames t) (exportNormalize renames b) i)
    | .letE _ t v b n => some (.letE .anonymous (exportNormalize renames t) (exportNormalize renames v) (exportNormalize renames b) n)
    | _ => none

partial def encodeLevel : Level → Json
  | .zero => toJson (["zero"] : List String)
  | .succ u => Json.arr #[toJson "succ", encodeLevel u]
  | .max u v => Json.arr #[toJson "max", encodeLevel u, encodeLevel v]
  | .imax u v => Json.arr #[toJson "imax", encodeLevel u, encodeLevel v]
  | .param n => Json.arr #[toJson "param", toJson n.toString]
  | .mvar _ => panic! "Unexpected universe metavariable"

partial def decodeLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => return .zero
  | "succ" => return .succ (← decodeLevel a[1]!)
  | "max" => return .max (← decodeLevel a[1]!) (← decodeLevel a[2]!)
  | "imax" => return .imax (← decodeLevel a[1]!) (← decodeLevel a[2]!)
  | "param" => return .param (← a[1]!.getStr?).toName
  | _ => throw "Unexpected level node"

structure ExprTable where
  index : Std.HashMap Expr Nat := {}
  nodes : Array Json := #[]

def binderCode : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

def decodeBinder (i : Nat) : BinderInfo :=
  match i with
  | 1 => .implicit
  | 2 => .strictImplicit
  | 3 => .instImplicit
  | _ => .default

partial def encodeExpr (e : Expr) : StateM ExprTable Nat := do
  if let some i := (← get).index[e]? then return i
  let node : Json ← match e with
    | .bvar i => pure (Json.arr #[toJson "bvar", toJson i])
    | .sort u => pure (Json.arr #[toJson "sort", encodeLevel u])
    | .const n us => pure (Json.arr #[toJson "const", toJson n.toString, Json.arr (us.toArray.map encodeLevel)])
    | .app f x => pure (Json.arr #[toJson "app", toJson (← encodeExpr f), toJson (← encodeExpr x)])
    | .lam _ t b i => pure (Json.arr #[toJson "lam", toJson (← encodeExpr t), toJson (← encodeExpr b), toJson (binderCode i)])
    | .forallE _ t b i => pure (Json.arr #[toJson "forall", toJson (← encodeExpr t), toJson (← encodeExpr b), toJson (binderCode i)])
    | .letE _ t v b n => pure (Json.arr #[toJson "let", toJson (← encodeExpr t), toJson (← encodeExpr v), toJson (← encodeExpr b), toJson n])
    | .lit (.natVal n) => pure (Json.arr #[toJson "nat", toJson n])
    | .lit (.strVal s) => pure (Json.arr #[toJson "str", toJson s])
    | .proj n i s => pure (Json.arr #[toJson "proj", toJson n.toString, toJson i, toJson (← encodeExpr s)])
    | .mdata _ v => encodeExpr v >>= fun i => pure (Json.arr #[toJson "alias", toJson i])
    | _ => panic! "Unexpected free expression variable"
  let i := (← get).nodes.size
  modify fun s => { index := s.index.insert e i, nodes := s.nodes.push node }
  return i

def decodeExprTable (nodes : Array Json) : Except String (Array Expr) := do
  let mut result : Array Expr := #[]
  for node in nodes do
    let a ← node.getArr?
    let child := fun (i : Nat) => do
      let n ← a[i]!.getNat?
      if h : n < result.size then return result[n] else throw "Invalid expression DAG"
    let expr : Expr ← match ← a[0]!.getStr? with
      | "bvar" => pure (.bvar (← a[1]!.getNat?))
      | "sort" => pure (.sort (← decodeLevel a[1]!))
      | "const" => do
        let us ← (← a[2]!.getArr?).toList.mapM decodeLevel
        pure (.const (← a[1]!.getStr?).toName us)
      | "app" => pure (.app (← child 1) (← child 2))
      | "lam" => pure (.lam .anonymous (← child 1) (← child 2) (decodeBinder (← a[3]!.getNat?)))
      | "forall" => pure (.forallE .anonymous (← child 1) (← child 2) (decodeBinder (← a[3]!.getNat?)))
      | "let" => pure (.letE .anonymous (← child 1) (← child 2) (← child 3) (← a[4]!.getBool?))
      | "nat" => pure (.lit (.natVal (← a[1]!.getNat?)))
      | "str" => pure (.lit (.strVal (← a[1]!.getStr?)))
      | "proj" => pure (.proj (← a[1]!.getStr?).toName (← a[2]!.getNat?) (← child 3))
      | "alias" => child 1
      | _ => throw "Unexpected expression node"
    result := result.push expr
  return result
