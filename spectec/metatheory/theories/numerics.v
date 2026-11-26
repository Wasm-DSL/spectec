From Stdlib Require Import List String NArith ZArith QArith.
From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory.
From MetaSpectec Require Import syntax.

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
  | EquivOp => (b1 ==> b2) && (b2 ==> b1)
  end
.

(* Stdlib rationals: comparisons and normal form *)

Definition Qlt_bool (x y : Q) : bool := negb (Qle_bool y x).

(* Q -> Z, if the rational is an integer *)
Definition Q_to_Z (q : Q) : option Z :=
  let q' := Qred q in
  if Pos.eqb (Qden q') 1 then Some (Qnum q') else None.

(* Embeddings into the reals *)

Definition N_to_R (n : N) : R := ((N.to_nat n)%:R)%R.

Definition Z_to_R (z : Z) : R :=
  if Z.ltb z 0 then (- ((Z.to_nat (- z))%:R))%R else ((Z.to_nat z)%:R)%R.

Definition Q_to_R (q : Q) : R :=
  (Z_to_R (Qnum q) / ((Pos.to_nat (Qden q))%:R))%R.

Definition iszero (x : il_num) : bool :=
  match x with
  | NatE n => N.eqb n 0
  | IntE i => Z.eqb i 0
  | RatE q => Qeq_bool q 0
  | RealE r => (r == 0)%R
  end
.

Definition isone (x : il_num) : bool :=
  match x with
  | NatE n => N.eqb n 1
  | IntE i => Z.eqb i 1
  | RatE q => Qeq_bool q 1
  | RealE r => (r == 1)%R
  end
.

Definition isneg (x : il_num) : bool :=
  match x with
  | NatE n => false
  | IntE i => Z.ltb i 0
  | RatE q => Qlt_bool q 0
  | RealE r => (r < 0)%R
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

Definition int_to_nat_num (x : Z) : option il_num :=
  if Z.leb 0 x then Some (NatE (Z.to_N x)) else None.

(* $numcvt for sources other than REAL, and REAL -> REAL *)
Definition numcvt (nt : numtyp) (val : il_num) : option il_num :=
  match nt, val with
  | NatT, NatE n => Some (NatE n)
  | NatT, IntE i => int_to_nat_num i
  | NatT, RatE q => option_join (option_map int_to_nat_num (Q_to_Z q))
  | IntT, NatE n => Some (IntE (Z.of_N n))
  | IntT, IntE i => Some (IntE i)
  | IntT, RatE q => option_map IntE (Q_to_Z q)
  | RatT, NatE n => Some (RatE (inject_Z (Z.of_N n)))
  | RatT, IntE i => Some (RatE (inject_Z i))
  | RatT, RatE q => Some (RatE (Qred q))
  | RealT, NatE n => Some (RealE (N_to_R n))
  | RealT, IntE i => Some (RealE (Z_to_R i))
  | RealT, RatE q => Some (RealE (Q_to_R q))
  | RealT, RealE r => Some (RealE r)
  (* Handled by num_cvt: whether a real is rational is not decidable *)
  | _, RealE _ => None
  end
.

Definition is_real_to_exact (nt : numtyp) (val : il_num) : bool :=
  match nt, val with
  | RealT, _ => false
  | _, RealE _ => true
  | _, _ => false
  end.

(* $numcvt as a (functional) relation; None = undefined.
   DSL: $numcvt(nt, REAL r) = $numcvt(nt, RAT $rat$(r))  -- if r = $rat$(r)
   (Qred makes the result independent of the representative q) *)
Inductive num_cvt : numtyp -> il_num -> option il_num -> Prop :=
  | ncvt_exact : forall nt val,
    ~~ is_real_to_exact nt val ->
    num_cvt nt val (numcvt nt val)
  | ncvt_real_rat : forall nt q,
    is_real_to_exact nt (RealE (Q_to_R q)) ->
    num_cvt nt (RealE (Q_to_R q)) (numcvt nt (RatE (Qred q)))
  | ncvt_real_irrat : forall nt r,
    is_real_to_exact nt (RealE r) ->
    (forall q, r <> Q_to_R q) ->
    num_cvt nt (RealE r) None
.

Definition numun (op : numunop) (val : il_num) : option il_num :=
  match op, val with
  | PlusOp, n => Some n
  | MinusOp, NatE n => Some (IntE (Z.opp (Z.of_N n)))
  | MinusOp, IntE i => Some (IntE (Z.opp i))
  | MinusOp, RatE q => Some (RatE (Qred (Qopp q)))
  | MinusOp, RealE r => Some (RealE (- r)%R)
  end
.

Definition numbin (op : numbinop) (val1 val2 : il_num) : option il_num :=
  match op, val1, val2 with
  | AddOp, NatE n1, NatE n2 => Some (NatE (N.add n1 n2))
  | AddOp, IntE i1, IntE i2 => Some (IntE (Z.add i1 i2))
  | AddOp, RatE q1, RatE q2 => Some (RatE (Qred (Qplus q1 q2)))
  | AddOp, RealE r1, RealE r2 => Some (RealE (r1 + r2)%R)
  | SubOp, NatE n1, NatE n2 => if N.leb n2 n1 then Some (NatE (N.sub n1 n2)) else None
  | SubOp, IntE i1, IntE i2 => Some (IntE (Z.sub i1 i2))
  | SubOp, RatE q1, RatE q2 => Some (RatE (Qred (Qminus q1 q2)))
  | SubOp, RealE r1, RealE r2 => Some (RealE (r1 - r2)%R)
  | MulOp, NatE n1, NatE n2 => Some (NatE (N.mul n1 n2))
  | MulOp, IntE i1, IntE i2 => Some (IntE (Z.mul i1 i2))
  | MulOp, RatE q1, RatE q2 => Some (RatE (Qred (Qmult q1 q2)))
  | MulOp, RealE r1, RealE r2 => Some (RealE (r1 * r2)%R)
  (* NAT and INT division must be exact *)
  | DivOp, NatE n1, NatE n2 =>
    if negb (iszero val2) && N.eqb (N.modulo n1 n2) 0 then Some (NatE (N.div n1 n2)) else None
  | DivOp, IntE i1, IntE i2 =>
    if negb (iszero val2) && Z.eqb (Z.modulo i1 i2) 0 then Some (IntE (Z.div i1 i2)) else None
  | DivOp, RatE q1, RatE q2 => if negb (iszero val2) then Some (RatE (Qred (Qdiv q1 q2))) else None
  | DivOp, RealE r1, RealE r2 => if negb (iszero val2) then Some (RealE (r1 / r2)%R) else None
  (* The DSL does not fix the sign convention of INT modulo; Z.modulo takes
     the sign of the divisor *)
  | ModOp, NatE n1, NatE n2 => if negb (iszero val2) then Some (NatE (N.modulo n1 n2)) else None
  | ModOp, IntE i1, IntE i2 => if negb (iszero val2) then Some (IntE (Z.modulo i1 i2)) else None
  | PowOp, NatE n1, NatE n2 => Some (NatE (N.pow n1 n2))
  | PowOp, IntE i1, IntE i2 => if Z.leb 0 i2 then Some (IntE (Z.pow i1 i2)) else None
  | PowOp, RatE q1, RatE q2 =>
    option_map (fun z => RatE (Qred (Qpower q1 z))) (Q_to_Z q2)
  | PowOp, RealE r1, RealE r2 => Some (RealE (powR r1 r2))
  | _, _, _ => None
  end
.

Definition numcmp (op : numcmpop) (val1 val2 : il_num) : option bool :=
  match op, val1, val2 with
  | LtOp, NatE n1, NatE n2 => Some (N.ltb n1 n2)
  | LtOp, IntE i1, IntE i2 => Some (Z.ltb i1 i2)
  | LtOp, RatE q1, RatE q2 => Some (Qlt_bool q1 q2)
  | LtOp, RealE r1, RealE r2 => Some (r1 < r2)%R
  | GtOp, NatE n1, NatE n2 => Some (N.ltb n2 n1)
  | GtOp, IntE i1, IntE i2 => Some (Z.ltb i2 i1)
  | GtOp, RatE q1, RatE q2 => Some (Qlt_bool q2 q1)
  | GtOp, RealE r1, RealE r2 => Some (r1 > r2)%R
  | LeOp, NatE n1, NatE n2 => Some (N.leb n1 n2)
  | LeOp, IntE i1, IntE i2 => Some (Z.leb i1 i2)
  | LeOp, RatE q1, RatE q2 => Some (Qle_bool q1 q2)
  | LeOp, RealE r1, RealE r2 => Some (r1 <= r2)%R
  | GeOp, NatE n1, NatE n2 => Some (N.leb n2 n1)
  | GeOp, IntE i1, IntE i2 => Some (Z.leb i2 i1)
  | GeOp, RatE q1, RatE q2 => Some (Qle_bool q2 q1)
  | GeOp, RealE r1, RealE r2 => Some (r1 >= r2)%R
  | _, _, _ => None
  end
.
