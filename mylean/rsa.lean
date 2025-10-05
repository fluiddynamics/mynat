import mynat
import binom
import modulo
open MyNat

@[aesop unsafe]
theorem lt01 : 0<1 := by
apply lt_le_succ.2
exists 0

section rsa

variable (p:MyNat) (q:MyNat)
variable (pp : is_prime p)
variable (qp : is_prime q)
include pp qp

@[aesop unsafe]
theorem pq1 : 1<p*q := by
apply lt_le_succ.2
rcases (lt_le_succ.1 pp.1) with ⟨w,h ⟩
rcases (lt_le_succ.1 qp.1) with ⟨ww,hg ⟩
rewrite [<-h,<-hg]
rewrite [succ_add_one]
ring_nf
exists 2+w*2+w*ww+ww*2

variable (npq : p ≠ q)
include npq

local infix:50 " ≡p " => modulo.modeq p
local infix:50 " ≡q " => modulo.modeq q
local infix:50 " ≡pq " => modulo.modeq (p*q)

theorem crt1 a: p∣a -> q∣a -> (p*q)∣ a := by
intros b c
rcases b with ⟨w,h⟩
have d := pabpapb q p w qp ?_
cases d with
|inl hh =>
  exfalso
  have pp1 := pp.2 q hh
  cases pp1 with
  |inl hhh =>
    apply qp.1.2
    aesop
  |inr hhh =>
    apply npq
    aesop
|inr hh =>
  rcases hh with ⟨ww,hhh⟩
  rewrite [<-hhh] at h
  exists ww
  rewrite [<-h]
  ring
rewrite [h]
apply c


theorem crt2 a : a≡p 0 ∧ a≡q 0 ↔ a≡pq 0 := by
constructor
intros b
rcases b with ⟨b1,b2⟩
have c := (dvd_mod_0 p a ?_).2 ?_
have d := (dvd_mod_0 q a ?_).2 ?_
have cd := crt1 p q pp qp npq a c d
apply (dvd_mod_0 (p*q) a ?_).1 cd
apply MyNat.lt_trans
apply lt_le_succ.2
exists 0
apply pq1
apply pp
apply qp
apply MyNat.lt_trans
apply lt_le_succ.2
exists 0
apply qp.1
apply (dvd_mod_0 q a ?_).1
apply (dvd_mod_0 q a ?_).2
unfold modulo.modeq at b2
rewrite [b2]
rewrite [<-zero0]
simp
apply MyNat.lt_trans lt01 qp.1
apply MyNat.lt_trans lt01 qp.1
apply MyNat.lt_trans lt01 pp.1
rewrite [b1]
rewrite [<-zero0]
simp
intros b
have bb := (dvd_mod_0 (p*q) a ?_).2 ?_
rcases bb with ⟨w,h ⟩
constructor
apply (dvd_mod_0 _ _ ?_).1
exists q*w
rewrite [<-h]
ring
apply MyNat.lt_trans lt01 pp.1
unfold modulo.modeq
rewrite [<-zero0]
simp
apply (dvd_mod_0 _ _ ?_).1
exists p*w
rewrite [<-h]
ring
apply MyNat.lt_trans lt01 qp.1
apply MyNat.lt_trans lt01
apply pq1
apply pp
apply qp
rewrite [b]
rewrite [<-zero0]
simp

theorem crt3 a : (1+a)≡p 0 ∧ (1+a)≡q 0 ↔ (1+a)≡pq 0 := by
apply crt2
apply pp
apply qp
apply npq

theorem crt a : forall a', a≡p a' ∧ a≡q a' ↔ a≡pq a' := by
induction a with
|zero =>
  rewrite [zero0]
  intros a'
  constructor
  intros b
  have c2 := (crt2 p q pp qp npq a').1
  unfold modulo.modeq
  symm
  rewrite [<-modulo.modeq]
  apply c2
  unfold modulo.modeq
  rcases b with ⟨b1,b2 ⟩
  constructor
  symm
  apply b1
  symm
  apply b2
  intros b
  unfold modulo.modeq at b
  symm at b
  rewrite [<-modulo.modeq] at b
  have c3 := (crt2 p q pp qp npq a').2 b
  rcases c3 with ⟨d1,d2⟩
  unfold modulo.modeq at d1
  symm at d1
  rewrite [<-modulo.modeq] at d1
  unfold modulo.modeq at d2
  symm at d2
  rewrite [<-modulo.modeq] at d2
  constructor
  apply d1
  apply d2
|succ b ih =>
  intros b'
  have aaa := (modulo.mod_minus (p*q) 1 ?_)
  rcases aaa with ⟨ w,h⟩
  rcases ((crt3 p q pp qp npq w).2 h) with ⟨ p1,q1⟩
  have ih1 := ih (b'+w)
  simp
  constructor
  intros c
  apply modulo.mod_sym
  apply (modulo.minusone_cancel (p*q) w ?_ b' b).1
  apply modulo.mod_sym
  apply ih1.1
  rcases c with ⟨c1,c2 ⟩
  constructor
  apply modulo.mod_sym
  apply  (modulo.minusone_cancel p w ?_ b' b).2
  apply modulo.mod_sym
  apply c1
  apply p1
  apply modulo.mod_sym
  apply  (modulo.minusone_cancel q w ?_ b' b).2
  apply modulo.mod_sym
  apply c2
  apply q1
  apply h
  intros c
  constructor
  apply modulo.mod_sym
  apply (modulo.minusone_cancel p w ?_ b' b).1
  apply modulo.mod_sym
  have ih11 := ih1.2 ?_
  apply ih11.1
  apply modulo.mod_sym
  apply (modulo.minusone_cancel (p*q) w ?_ b' b).2
  apply modulo.mod_sym
  apply c
  apply h
  apply p1
  apply modulo.mod_sym
  apply (modulo.minusone_cancel q w ?_ b' b).1
  apply modulo.mod_sym
  have ih11 := ih1.2 ?_
  apply ih11.2
  apply modulo.mod_sym
  apply (modulo.minusone_cancel (p*q) w ?_ b' b).2
  apply modulo.mod_sym
  apply c
  apply h
  apply q1
  apply MyNat.lt_trans
  apply lt01
  apply pq1
  apply pp
  apply qp

variable (p':MyNat) (q':MyNat)
variable (eqp' : p' + 1 = p)
variable (eqq' : q' + 1 = q)
include eqp' eqq'

theorem rsa a : forall k, binomial.pow a (k*p'*q'+1) ≡pq a := by
intros k
apply (crt _ _ pp qp npq _ _).1
constructor
rewrite [mul_assoc]
rewrite [mul_comm]
rewrite [mul_assoc]
have z := pow_p_pred p a (q'*k) pp p' ?_
assumption
simp
assumption
rewrite [mul_comm]
apply pow_p_pred q a (k*p') qp q' ?_
simp
assumption

end rsa

structure linear where
  a:MyNat
  x:MyNat
  b:MyNat
  y:MyNat
  c:MyNat
  eq : a*x=b*y+c

def divmod_aux (n m:MyNat) : MyNat×MyNat×MyNat:= match m with
|zero => (0,n,0)
|succ m' => match n with
  | zero => (zero,zero,m')
  | succ n' =>
    let prev := divmod_aux n' m
    match prev.2.2 with
      | zero => (prev.1 + 1, zero, m')
      | succ p' => (prev.1, prev.2.1 + 1, p')

#eval divmod_aux 34 5
#eval divmod_aux 0 0

def aux1 (n m:MyNat) : m ≠ 0 -> let aux := divmod_aux n m; aux.2.1 + aux.2.2 + 1 = m := by
intros a
intros aux
have eq : aux = divmod_aux n m := by rfl
induction n with
|zero =>
  unfold divmod_aux at eq
  simp at eq
  split at eq
  exfalso
  apply a
  simp
  rewrite [eq]
  simp
| succ n' ih =>
  generalize eq' : divmod_aux n' m = aux'
  simp at ih
  rewrite [eq'] at ih
  unfold divmod_aux at eq
  split at eq
  simp at eq'
  rewrite [<-succ_add_one] at ih
  rewrite [succ_add] at ih
  injection ih
  case h_2 p' =>
    simp at eq
    split at eq
    rewrite [eq]
    simp
    case h_2 p'' p'''=>
      rewrite [eq]
      simp
      simp at eq'
      rewrite [eq'] at p'''
      rewrite [eq']
      rewrite [p'''] at ih
      simp at ih
      rewrite [<-ih]
      ring

def divmod (n m:MyNat) : linear := let aux := divmod_aux n m
  ⟨1,n,aux.1,m,aux.2.1,by
  induction n with
  |zero =>
    simp
    have eq : aux = divmod_aux zero m := by rfl
    unfold divmod_aux at eq
    simp at eq
    split at eq
    rewrite [eq]
    rfl
    rewrite [eq]
    simp
  |succ n' ih=>
    simp
    have eq : aux = divmod_aux n'.succ m := by rfl
    unfold divmod_aux at eq
    simp at eq
    split at eq
    rewrite [eq]
    simp
    split at eq
    case h_1 heq x p'=>
      generalize heq1 : heq.succ = m
      simp at ih
      generalize eqaux' : divmod_aux n' (heq+1) = aux'
      rewrite [eqaux'] at ih
      have z:aux'.1 + aux'.1*heq = aux'.1*m := by
        rewrite [<-heq1]
        simp
      rewrite [z] at ih
      rewrite [<-succ_add_one] at eqaux'
      rewrite [heq1] at eq
      rewrite [heq1] at eqaux'
      rewrite [eqaux'] at eq
      rewrite [eq]
      simp
      have aa := aux1 n' m ?_
      simp at aa
      rewrite [eqaux'] at aa
      conv =>
        rhs
        arg 1
        rewrite [<-aa]
      rewrite [ih]
      rewrite [heq1] at p'
      rewrite [eqaux'] at p'
      rewrite [p']
      simp
      ring
      intros m0
      rewrite [m0] at heq1
      rewrite [<-zero0] at heq1
      injection heq1
    case h_2 x1 m' x3 x4 x5=>
      generalize meq : m'.succ = m
      rewrite [meq] at ih
      rewrite [meq] at x5
      rewrite [meq] at eq
      generalize auxeq' : divmod_aux n' m = aux'
      rewrite [auxeq'] at eq
      simp at ih
      rewrite [auxeq'] at ih
      rewrite [eq]
      simp
      rewrite [ih]
      ring
  ⟩

#eval divmod 8 9
