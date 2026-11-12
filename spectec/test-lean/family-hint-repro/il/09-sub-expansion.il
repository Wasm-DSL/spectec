
;; test-lean/family-hint-repro/toy.spectec:5.1-5.39
syntax numtype = 
  | I32
  | I64
  | F32
  | F64

;; test-lean/family-hint-repro/toy.spectec:6.1-6.22
syntax vectype = 
  | V128

;; test-lean/family-hint-repro/toy.spectec:8.1-8.23
syntax Inn = 
  | I32
  | I64

;; test-lean/family-hint-repro/toy.spectec:9.1-9.23
syntax Fnn = 
  | F32
  | F64

;; test-lean/family-hint-repro/toy.spectec:10.1-10.18
syntax Vnn = 
  | V128

;; test-lean/family-hint-repro/toy.spectec:12.1-12.21
syntax num_ = 
  | mk_num__0(Inn : Inn, var_x : nat)
  | mk_num__1(Fnn : Fnn, var_x : nat)

;; test-lean/family-hint-repro/toy.spectec:12.8-12.13
relation wf_num_: `%%`(numtype, num_)
  ;; test-lean/family-hint-repro/toy.spectec:12.8-12.13
  rule num__case_0{numtype : numtype, Inn : Inn, var_x : nat}:
    `%%`(numtype, mk_num__0_num_(Inn, var_x))
    -- if (numtype = (Inn : Inn <: numtype))

  ;; test-lean/family-hint-repro/toy.spectec:12.8-12.13
  rule num__case_1{numtype : numtype, Fnn : Fnn, var_x : nat}:
    `%%`(numtype, mk_num__1_num_(Fnn, var_x))
    -- if (numtype = (Fnn : Fnn <: numtype))

;; test-lean/family-hint-repro/toy.spectec:12.1-12.21
def $proj_num__0(var_x : num_) : nat?
  ;; test-lean/family-hint-repro/toy.spectec:12.8-12.13
  def $proj_num__0{Inn : Inn, var_x : nat}(mk_num__0_num_(Inn, var_x)) = ?(var_x)
  ;; test-lean/family-hint-repro/toy.spectec:12.8-12.13
  def $proj_num__0{var_x : num_}(var_x) = ?()

;; test-lean/family-hint-repro/toy.spectec:12.1-12.21
def $proj_num__1(var_x : num_) : nat?
  ;; test-lean/family-hint-repro/toy.spectec:12.8-12.13
  def $proj_num__1{Fnn : Fnn, var_x : nat}(mk_num__1_num_(Fnn, var_x)) = ?(var_x)
  ;; test-lean/family-hint-repro/toy.spectec:12.8-12.13
  def $proj_num__1{var_x : num_}(var_x) = ?()

;; test-lean/family-hint-repro/toy.spectec:16.1-16.27
syntax vec_ = nat

;; test-lean/family-hint-repro/toy.spectec:18.1-18.55
def $foo(numtype : numtype, num_ : num_) : nat*?
  def $foo{x0 : numtype, x1 : num_}(x0, x1) = ?()
    -- otherwise

;; test-lean/family-hint-repro/toy.spectec:19.1-19.55
def $bar(vectype : vectype, vec_ : vec_) : nat*

