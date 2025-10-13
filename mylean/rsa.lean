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

section computational_Rsa

structure linear where
  a:MyNat
  x:MyNat
  b:MyNat
  y:MyNat
  c:MyNat

def linear_good (l:linear) := l.a*l.x=l.b*l.y+l.c

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
  ⟨1,n,aux.1,m,aux.2.1⟩

theorem divmod_good n m: linear_good (divmod n m) := by
  induction n with
  |zero =>
    unfold divmod
    unfold linear_good
    unfold divmod_aux
    simp
    split <;> simp
  |succ n' ih=>
    generalize dmeq' : divmod n' m = dm'
    generalize dmeq : divmod (n'.succ) m = dm
    rewrite [dmeq'] at ih
    unfold divmod at dmeq
    unfold divmod_aux at dmeq
    split at dmeq
    simp at dmeq
    rewrite [<-dmeq]
    unfold linear_good
    simp
    split at dmeq
    case h_1 heq =>
      injection heq
    case h_2 x p' xx p'' heq =>
      injection heq with a_eq
      rewrite [<-a_eq] at dmeq
      generalize meq: p'.succ = m
      rewrite [meq] at dmeq'
      rewrite [meq] at dmeq
      rewrite [<-dmeq]
      unfold linear_good
      simp
      split
      unfold divmod at dmeq'
      generalize eqaux : divmod_aux n' m = aux
      rewrite [eqaux] at dmeq'
      simp at dmeq'
      rewrite [<-dmeq'] at ih
      unfold linear_good at ih
      simp at ih
      simp
      have aux1 := aux1 n' m ?_
      {
        rewrite [eqaux] at aux1
        simp at aux1
        case h_1.refine_2 heq =>
        rewrite [eqaux] at heq
        rewrite [heq] at aux1
        simp at aux1
        rewrite [ih]
        conv =>
          rhs
          arg 1
          rewrite [<-aux1]
        ring_nf
      }
      {
        unfold Ne
        unfold Not
        intros a
        rewrite [a] at meq
        injection meq
      }
      {
        simp
        generalize eqaux : divmod_aux n' m = aux
        rewrite [<-dmeq'] at ih
        unfold divmod at ih
        rewrite [eqaux] at ih
        unfold linear_good at ih
        simp at ih
        rewrite [ih]
        ring_nf
      }

#eval divmod 8 9

def gcd (n m:MyNat) :Bool×linear := by
generalize eq :m=mm
match m with
|zero => exact ⟨true,⟨1,n,0,m,n⟩ ⟩
|succ c'=>
  generalize dmeq : divmod n m = dm
  rcases dm with ⟨_,_,q,_,r⟩
  let ⟨gcdb, ⟨a,_,b,_,c⟩ ⟩:= gcd m r -- 停止性の証明で等式がいらないためlet
  match gcdb with
  |true  => exact⟨false, ⟨a+b*q, m, b,     n, c⟩⟩  -- a*m=b*(n-q*m)+c
  |false => exact⟨true,  ⟨a,     n, b+a*q, m, c⟩⟩  -- a*(n-q*m)=b*m+c
termination_by toNat m
decreasing_by
{
  apply lt_tonat
  generalize dmeq1 : divmod n m = dm
  rewrite [dmeq1] at dmeq
  unfold divmod at dmeq1
  generalize eqaux : divmod_aux n m = aux
  rewrite [eqaux] at dmeq1
  simp at dmeq1
  have a1 := aux1 n m ?_
  rewrite [eqaux] at a1
  simp at a1
  have z:aux.2.1 = r := by aesop
  rewrite [eq]
  rewrite [z] at a1
  apply lt_le_succ.2
  exists aux.2.2
  simp
  rewrite [<-a1]
  ring
  unfold Ne
  intros a
  rewrite [a] at eq
  injection eq
}
-- 等式が消えてしまうのを防ぐためにgeneralizeとかを使っている

#print _root_.gcd._unary

theorem gcd_true : forall n m, let g := _root_.gcd n m; g.1 = true -> g.2.x = n ∧ g.2.y = m := by
{
  intros n m
  generalize eqg : _root_.gcd n m = g
  intros s t
  have seq : s=g := by aesop
  unfold _root_.gcd at eqg
  split at eqg
  simp at eqg
  rewrite [seq]
  rewrite [<-eqg]
  simp
  simp at eqg
  split at eqg
  aesop
  rewrite [seq]
  rewrite [<-eqg]
  simp
}

theorem gcd_false : forall n m, let g := _root_.gcd n m; g.1 = false -> g.2.x = m ∧ g.2.y = n := by
{
  intros n m
  generalize eqg : _root_.gcd n m = g
  intros s t
  have seq : s=g := by aesop
  unfold _root_.gcd at eqg
  split at eqg
  aesop
  simp at eqg
  split at eqg
  rewrite [seq]
  rewrite [<-eqg]
  simp
  aesop
}

#check linear.casesOn

theorem gcd_good : forall n m, linear_good (_root_.gcd n m).2 := by
{
  intros n m
  fun_induction (_root_.gcd n m)
  case case1 =>
    simp
    unfold linear_good
    simp
  case case2 n c' x ih1=>
    simp
    generalize eqm : c'+1=m
    generalize eqdm : (divmod n m) = dm
    generalize eqgcd : _root_.gcd m dm.c = gcd'
    split
    case h_1 gcdn heq =>
      unfold linear_good
      simp
      simp at ih1
      rewrite [eqm] at ih1
      have ih11 := ih1 dm.1 dm.2 dm.3 dm.4 dm.5 ?_
      rewrite [eqgcd] at ih11
      unfold linear_good at ih11
      have g1 := gcd_true m dm.c
      simp at g1
      rewrite [eqgcd] at g1
      have g1 := g1 heq
      rcases g1 with ⟨ g2,g3⟩
      rewrite [g2] at ih11
      rewrite [g3] at ih11
      ring_nf
      have dmg := divmod_good n m
      unfold linear_good at dmg
      unfold divmod at dmg
      simp at dmg
      have z : (divmod_aux n m).2.1 = dm.c := by
        rewrite [<-eqdm]
        unfold divmod
        simp
      rewrite [z] at dmg
      have z : (divmod_aux n m).1 = dm.b := by
        rewrite [<-eqdm]
        unfold divmod
        simp
      rewrite [z] at dmg
      rewrite [dmg]
      rewrite [mul_dist]
      rewrite [ih11]
      ring_nf
      rewrite [eqdm]
      simp
    case h_2 gcdb heq =>
      unfold linear_good
      simp
      have gf := gcd_false m dm.c
      simp at gf
      rewrite [eqgcd] at gf
      have heq := gf heq
      rcases heq with ⟨ eq1,eq2⟩
      simp at ih1
      rewrite [eqm] at ih1
      have ih1 := ih1 dm.1 dm.2 dm.3 dm.4 dm.5 ?_
      rewrite [eqgcd] at ih1
      unfold linear_good at ih1
      have dmg := divmod_good n m
      rewrite [eqdm] at dmg
      unfold linear_good at dmg
      unfold divmod at eqdm
      simp at eqdm
      have dm1 : 1=dm.a := by rw [<-eqdm]
      have dm2 : n=dm.x := by rw [<-eqdm]
      have dm3 : m=dm.y := by rw [<-eqdm]
      rewrite [<-dm1] at dmg
      rewrite [<-dm2] at dmg
      rewrite [<-dm3] at dmg
      simp at dmg
      rewrite [dmg]
      rewrite [eq1] at ih1
      rewrite [mul_dist]
      rewrite [ih1]
      rewrite [eq2]
      ring_nf
      rewrite [eqdm]
      simp
}
