From Stdlib Require Import List String.
From mathcomp Require Import all_ssreflect all_algebra ssrnat ssrint.
Import GRing.Theory.
From MetaSpectec Require Import syntax.

Coercion absz : int >-> nat.

Coercion ratz: int >-> rat.

(* Booleans *)

Definition boolun (op : boolunop) (b : bool) : bool :=
  match op with
  | NotOp => negb b
  end
.

Definition boolbin (op : boolbinop) (b1 b2 : bool) : bool :=
  match op with
  | AndOp => b1 && b2
  | OrOp => b1 || b2
  | ImplOp => b1 ==> b2
  | EquivOp => b1 ==> b2 && b2 ==> b1
  end
.

Definition iszero(x : il_num) : bool := 
  match x with
  | NatE n => n == 0%nat
  | IntE i => i == 0%R
  | RatE r => r == 0%R
  | RealE r => r == 0%R
  end
.

Definition isone(x : il_num) : bool := 
  match x with
  | NatE n => n == 1%nat
  | IntE i => i == 1%R
  | RatE r => r == 1%R 
  | RealE r => r == 1%R
  end
.

Definition option_map {α β : Type} (f : α -> β) (x : option α) : option β :=
	match x with
  | Some x => Some (f x)
  | _ => None
	end.

Definition option_join {α : Type} (x : option (option α)) : option α :=
  match x with
  | Some None => None
  | None => None
  | Some (Some x') => Some x'
  end.

(* Numerics *)

Definition rat_to_int (x : rat) : option int :=
  if isone (IntE (denq x)) then Some (numq x) else None
.

Definition int_to_nat_num (x : int) : option il_num :=
  if (x >= 0)%R then Some (NatE x) else None.

Definition to_nat (x : R) : nat :=
  (Num.floor x).

Definition rat_to_R (q : rat) : R :=
  ((numq q)%:~R / (denq q)%:~R)%R.

(* TODO finish some of the conversions - especially for reals *)
Definition numcvt (nt : numtyp) (val : il_num) : option il_num :=
  match nt, val with
  | NatT, NatE n => Some (NatE n)
  | NatT, IntE i => int_to_nat_num i
  | NatT, RatE r => let opt := rat_to_int r in
    option_join (option_map (fun i => int_to_nat_num i) opt)
  | NatT, RealE r => Some (NatE (to_nat r))
  | IntT, NatE n => Some (IntE n)
  | IntT, IntE i => Some (IntE i)
  | IntT, RatE r => if isone (IntE (denq r)) then Some (IntE (numq r)) else None
  | IntT, RealE r => Some (IntE (Num.floor r))
  | RatT, NatE n => Some (RatE (n%:Q))
  | RatT, IntE i => Some (RatE (i%:Q))
  | RatT, RatE r => Some (RatE r)
  (* TODO think of a better way to cvt real to rational *)
  | RatT, RealE r => Some (RatE (Num.floor r)%:Q)
  | RealT, NatE n => Some (RealE (n%:R))
  | RealT, IntE i => Some (RealE (i%:R))
  | RealT, RatE r => Some (RealE (rat_to_R r))
  | RealT, RealE r => Some (RealE r)
  end
.

Definition numun (op : numunop) (val : il_num) : option il_num :=
  match op, val with
  | PlusOp, n => Some n
  | MinusOp, NatE n => Some (IntE (0 - n%:R)%R) 
  | MinusOp, IntE i => Some (IntE (0 - i)%R)
  | MinusOp, RatE r => Some (RatE (0 - r)%R)
  | MinusOp, RealE r => Some (RealE (0 - r)%R)
  end
.

Definition numbin (op : numbinop) (val1 val2 : il_num) : option il_num :=
  match op, val1, val2 with
  | AddOp, NatE n1, NatE n2 => Some (NatE (n1 + n2)%nat)
  | AddOp, IntE i1, IntE i2 => Some (IntE (i1 + i2)%R)
  | AddOp, RatE r1, RatE r2 => Some (RatE (r1 + r2)%R)
  | AddOp, RealE r1, RealE r2 => Some (RealE (r1 + r2)%R)
  | SubOp, NatE n1, NatE n2 => if (n1 >= n2)%nat then Some (NatE (n1 - n2)%nat) else None
  | SubOp, IntE i1, IntE i2 => Some (IntE (i1 - i2)%R)
  | SubOp, RatE r1, RatE r2 => Some (RatE (r1 - r2)%R)
  | SubOp, RealE r1, RealE r2 => Some (RealE (r1 - r2)%R)
  | MulOp, NatE n1, NatE n2 => Some (NatE (n1 * n2)%nat)
  | MulOp, IntE i1, IntE i2 => Some (IntE (i1 * i2)%R)
  | MulOp, RatE r1, RatE r2 => Some (RatE (r1 * r2)%R)
  | MulOp, RealE r1, RealE r2 => Some (RealE (r1 * r2)%R)
  | DivOp, NatE n1, NatE n2 => if negb (iszero val2) then Some (NatE (Nat.div n1 n2)) else None
  | DivOp, IntE i1, IntE i2 => if negb (iszero val2) then Some (IntE (divz i1 i2)) else None
  | DivOp, RatE r1, RatE r2 => if negb (iszero val2) then Some (RatE (r1 / r2)%R) else None
  | DivOp, RealE r1, RealE r2 => if negb (iszero val2) then Some (RealE (r1 / r2)%R) else None
  | ModOp, NatE n1, NatE n2 => if negb (iszero val2) then Some (NatE (Nat.modulo n1 n2)) else None
  | ModOp, IntE i1, IntE i2 => if negb (iszero val2) then Some (NatE (modz i1 i2)) else None
  | PowOp, NatE n1, NatE n2 => Some (NatE (n1^n2))
  | PowOp, IntE i1, IntE i2 => if (i2 >= 0)%R then Some (IntE (i1^i2)) else None 
  | PowOp, RatE r1, RatE r2 => if isone (IntE (denq r2)) then Some (RatE (r1^(numq r2))) else None 
  (* TODO - don't know how this is supposed to work: 
  | PowOp, RealE r1, RealE r2 => RealE (r1^r2) *)
  | _, _, _ => None
  end
.


Definition numcmp (op : numcmpop) (val1 val2 : il_num) : option bool :=
  match op, val1, val2 with
  | LtOp, NatE n1, NatE n2 => Some ((n1 < n2)%nat)
  | LtOp, IntE i1, IntE i2 => Some ((i1 < i2)%R)
  | LtOp, RatE r1, RatE r2 => Some ((r1 < r2)%R)
  | LtOp, RealE r1, RealE r2 => Some ((r1 < r2)%R)
  | GtOp, NatE n1, NatE n2 => Some ((n1 > n2)%nat)
  | GtOp, IntE i1, IntE i2 => Some ((i1 > i2)%R)
  | GtOp, RatE r1, RatE r2 => Some ((r1 > r2)%R)
  | GtOp, RealE r1, RealE r2 => Some ((r1 > r2)%R)
  | LeOp, NatE n1, NatE n2 => Some ((n1 <= n2)%nat)
  | LeOp, IntE i1, IntE i2 => Some ((i1 <= i2)%R)
  | LeOp, RatE r1, RatE r2 => Some ((r1 <= r2)%R)
  | LeOp, RealE r1, RealE r2 => Some ((r1 <= r2)%R)
  | GeOp, NatE n1, NatE n2 => Some ((n1 >= n2)%nat)
  | GeOp, IntE i1, IntE i2 => Some ((i1 >= i2)%R)
  | GeOp, RatE r1, RatE r2 => Some ((r1 >= r2)%R)
  | GeOp, RealE r1, RealE r2 => Some ((r1 >= r2)%R)
  | _, _, _ => None
  end
.