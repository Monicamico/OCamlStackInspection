(* Tipi di permessi *)
type permission =
  | ReadPerm of string
  | WritePerm of string
  | ExecutePerm of string

(* Tabella dei permessi, contiene coppie di tipo (nome_funzione, lista_permessi) *)
type permissionTable = (string * permission list) list

(* Lista di funzioni chiamate *)
type stack = string list 

type gstate = GState of int;;

let isEqualPermission perm1 perm2 = 
  begin 
    match perm1, perm2 with
    | ReadPerm(f1), ReadPerm(f2) -> if f1 = f2 then true else false
    | WritePerm(f1), WritePerm(f2) -> if f1 = f2 then true else false
    | ExecutePerm(f1), ExecutePerm(f2) -> if f1 = f2 then true else false
    | _ -> false
  end;;

(* Data la Tabella dei permessi e una funzione f, 
  restituisce la lista dei permessi della funzione f *)
let rec getPerms (permList: permissionTable) (f: string) = 
  begin 
    match permList with
    |(y,pl)::xs -> if f=y then pl else getPerms xs f
    |[]-> []
  end;;

(* Controlla che il permesso {e} sia presente nella lista {l} *)
let rec isIn e l = begin
                    match l with 
                    | [] -> false
                    | y::ys -> if isEqualPermission e y then true else isIn e ys
                  end;;

(* An environment is a map from identifier to a value (what the identifier is bound to).
  For simplicity we represent the environment as an association list, i.e., a list of pair (identifier, data).
*)
type 'v env = (string * 'v) list;;

(**
  Given an environment {env} and an identifier {x} it returns the data {x} is bound to.
  If there is no binding, it raises an exception.
*)
let rec lookup env x =
  match env with
  | []        -> failwith (x ^ " not found")
  | (y, v)::r -> if x=y then v else lookup r x;;

(** 
Intermediate representation:
	expressions extended with Abort routine and global state manipulation
*)

type iexpr =
  | CstI of int
  | CstB of bool
  | Var of string
  | CstS of string (* costante stringa *)
  | Let of string * iexpr * iexpr
  | Prim of string * iexpr * iexpr
  | If of iexpr * iexpr * iexpr
  | Fun of string * iexpr * permission list
  | Call of iexpr * iexpr
  | Read of iexpr
  | Write of iexpr
  | Execute of iexpr
  | Abort of string
  | GLet of iexpr * iexpr
  | GVar;;
 
type ivalue =
  | Int of int
  | Str of string
  | Closure of string * iexpr * ivalue env * permission list;;

(* Controlla che tutte le funzioni presenti nello stack abbiano il permesso {perm} *)
let check (stack: stack) (permTable: permissionTable) (perm: permission) = 
  let rec getStackPermissions (s: stack) : (permission list) list = match s with 
    | []-> []
    | x::xs -> (getPerms permTable x)::getStackPermissions xs
  in let rec checkAll ll = match ll with
      | [z] -> isIn perm z 
      | z::zs -> isIn perm z && checkAll zs
      | _ -> false
  in checkAll (getStackPermissions stack);;
 
 
let rec ieval (e : iexpr) (env : ivalue env) (callStack: stack) (permTable: permissionTable) (g : gstate) : ivalue * gstate  =
  match e with
  | CstI i -> (Int i, g)
  | CstB b -> (Int (if b then 1 else 0), g)
  | CstS s -> (Str s, g)
  | Var x  -> (lookup env x, g)
  | Prim(ope, e1, e2) ->
      let (v1, g') = ieval e1 env callStack permTable g in
      let (v2, g'') = ieval e2 env callStack permTable g' in
      begin
        match (ope, v1, v2) with
        | ("*", Int i1, Int i2) -> (Int (i1 * i2), g'')
        | ("+", Int i1, Int i2) -> (Int (i1 + i2), g'')
        | ("-", Int i1, Int i2) -> (Int (i1 - i2), g'')
        | ("=", Int i1, Int i2) -> (Int (if i1 = i2 then 1 else 0), g'')
        | ("<", Int i1, Int i2) -> (Int (if i1 < i2 then 1 else 0), g'')
        |  _ -> failwith "unknown primitive or wrong type"
      end
  | Let(x, eRhs, ltBody) ->
      let (xVal, g') = ieval eRhs env callStack permTable g in
      let ltEnv = (x, xVal) :: env in
      ieval ltBody ltEnv callStack permTable g'
  | If(e1, e2, e3) ->
      begin
        match ieval e1 env callStack permTable g with
        | (Int 0, g') -> ieval e3 env callStack permTable g'
        | (Int _, g') -> ieval e2 env callStack permTable g'
        | _     -> failwith "eval If"
      end
  | Fun(x,fBody, perm) -> (Closure(x, fBody, env, perm), g) (* perm = permessi associati alla funzione *)
  | Call(eFun, eArg) ->
      let (fClosure, _) = ieval eFun env callStack permTable g in
      begin
        match fClosure with
        | Closure (x, fBody, fDeclEnv, fDeclPerm) -> let (xVal, g') = ieval eArg env callStack permTable g in
            let fBodyEnv = (x, xVal) :: fDeclEnv
            in ieval fBody fBodyEnv ([x] @ callStack) ((x,fDeclPerm) :: permTable) g' 
                                               
        | _ -> failwith "eval Call: not a function" 
      end
  | Read(x) -> begin 
              match ieval x env callStack permTable g with 
              | (Str s, _) -> let readperm = ReadPerm(s) in if check callStack permTable readperm then (Str s, g) else failwith "Read: permission denied"
              | _ -> failwith "Not a file"
              end
  | Write(x) -> begin 
                match ieval x env callStack permTable g with 
                | (Str s, _) -> let writeperm = WritePerm(s) in if check callStack permTable writeperm then (Str s, g) else failwith "Write: permission denied"
                | _ -> failwith "Not a file"
                end
  | Execute(x) -> begin 
                  match ieval x env callStack permTable g with 
                  | (Str s, _) -> let execperm = ExecutePerm(s) in if check callStack permTable execperm then (Str s, g) else failwith "Exec: permission denied"
                  | _ -> failwith "Not a file"
                  end
  | Abort msg -> failwith msg
  | GLet(ltVal, ltBody) -> let (xVal, _) = ieval ltVal env callStack permTable g 
      in begin match xVal with 
        | Int(i) -> ieval ltBody env callStack permTable (GState i)
        | _ -> failwith "eval Call: not an integer"
      end
  | GVar -> begin match g with
      | GState(i) -> (Int(i), g) 
    end
;;


(*  ESEMPI DI ESECUZIONE *)

let g = GState(0);; 

(* Programma che legge il file "file" chiamando la funzione chiamaf(p("file")) *)

let readFile = Fun("k",Read(Var("k")),[ReadPerm "file"]);;

let callReadFile = Fun("y",Call(readFile,Var("y")), [ReadPerm "file"]);;

let program = Let("z", CstS("file"),Call(callReadFile,Var("z")));;

ieval program [] [] [] g;;



(* Programma che tenta di leggere il file "file", ma le funzioni sullo stack non possiedono i permessi *)

let readFile1 = Fun("k",Read(Var("k")),[WritePerm "file1"]);;

let callReadFile1 = Fun("y",Call(readFile1,Var("y")), [ReadPerm "file1"]);;

let programErr = Let("z", CstS("file"),Call(callReadFile1,Var("z")));;

ieval programErr [] [] [] g;;


(* Programma che scrive su un file "b" *)

let writeFile = Fun("p", Write(Var("p")), [ WritePerm "a"; WritePerm "b"]);;

let programWriteOk = Let("g", CstS("b"), Call(writeFile, Var("g")));;

ieval programWriteOk [] [] [] g;;

(* Programma che tenta di scrivere su un file "s" ma la funzione non ha i permessi *)

let writeFileE = Fun("p", Write(Var("p")), [ WritePerm "a"; WritePerm "b"]);;

let programWriteErr = Let("g", CstS("s"), Call(writeFileE, Var("g")));;

ieval programWriteErr [] [] [] g;;