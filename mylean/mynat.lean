import Aesop
import Mathlib.Tactic.Ring


-- 1. 独自の自然数型 MyNat を定義します
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

-- MyNat 型に Lean の標準機能（表示など）を対応させます
namespace MyNat

-- MyNat の値を文字列で表示するための設定
def toNat : MyNat → Nat
  | zero => 0
  | succ n => Nat.succ ( toNat n )

def fromNat : Nat → MyNat
  | Nat.zero => zero
  | Nat.succ n => succ (fromNat n)

instance : OfNat MyNat n where
  ofNat:= fromNat n

instance : Repr MyNat where
  reprPrec n _ := s!"{toNat n}"

#check (0 : MyNat)
#check (succ (succ zero))
#check (2:MyNat)

-- 2. 演算の定義
@[aesop unsafe,simp]
def repeatn (f:MyNat -> MyNat) (n:MyNat) i:=
match n with
| zero => i
| succ n' => f (repeatn f n' i)

-- 足し算は+1の繰り返し
@[aesop unsafe,simp]
def addn (n:MyNat) : MyNat -> MyNat := repeatn succ n
@[aesop unsafe 50% apply]
def add (n m : MyNat) : MyNat := addn n m
-- 掛け算は+nの繰り返し
@[aesop unsafe 50% apply]
def mul (n m:MyNat) : MyNat := repeatn (addn n) m 0

instance:Add MyNat where add:=add
instance:Mul MyNat where mul:=mul


#eval ((3:MyNat) + (4:MyNat))
#eval ((3:MyNat) * (4:MyNat))

-- 3. 定理の証明

@[aesop safe,simp]
theorem add_zero (n : MyNat) : zero + n = n:= by aesop
@[aesop safe,simp]
theorem zero_add (n:MyNat) : n + zero = n := by
induction n with
| zero => aesop
| succ a ih=>
unfold instHAdd at *
unfold Add.add at *
unfold HAdd.hAdd at *
unfold instAdd at *
unfold add at *
aesop

@[aesop safe,simp]
theorem add_succ (n m:MyNat) : n.succ + m = (n+m).succ := by
aesop

@[aesop safe,simp]
theorem succ_add (n m:MyNat) : n + m.succ = (n+m).succ := by
induction n <;> aesop

--a+b = b+a
@[aesop unsafe,simp]
theorem add_comm (m n : MyNat) : m+n = n+m := by
induction n <;> aesop

@[aesop unsafe,simp]
theorem add_assoc (l m n:MyNat) : (l+m) +n = l + (m + n) := by
induction n <;> aesop

@[aesop unsafe]
theorem add_elim {n} {m} : n + m = n -> m = zero := by
induction n <;> aesop

@[aesop safe]
theorem add_eq_zero n m : n+m=zero -> m=zero := by
induction n <;> aesop

theorem add_abac {a b c:MyNat} : a+b=a+c <-> b=c := by
induction a <;> aesop

@[aesop safe,simp]
theorem mul_zero (n : MyNat) : zero * n = zero:= by
induction n <;> aesop

@[aesop safe,simp]
theorem zero_mul (n:MyNat) : n * zero = zero := by aesop

@[aesop safe]
theorem mul_one (m:MyNat) : m * zero.succ = m := by
induction m with
| zero => aesop
| succ m' ih =>
unfold instHMul at *
unfold Mul.mul at *
unfold HMul.hMul at *
unfold instMul at *
unfold mul at *
aesop

@[simp]
theorem one_mul (m:MyNat) : zero.succ * m = m := by
induction m with
| zero => aesop
| succ m' ih =>
unfold instHMul at *
unfold Mul.mul at *
unfold HMul.hMul at *
unfold instMul at *
unfold mul at *
aesop

@[aesop safe,simp]
theorem mul_succ (m n:MyNat) : m*(n.succ) = m + m*n := by
aesop

@[simp]
theorem succ_mul (m n:MyNat) : (m.succ)*n = n + m*n := by
induction n with
| zero => aesop
| succ a ih =>
rewrite [mul_succ]
rewrite [mul_succ]
rewrite [ih]
rewrite [add_succ]
rewrite [add_succ]
rewrite [<-add_assoc]
conv =>
  pattern m+a
  rewrite [add_comm]
rewrite [add_assoc]
rfl

--a*b = b*a
theorem mul_comm (n m : MyNat) : n*m = m*n := by
induction n <;> aesop

@[simp]
theorem mul_dist (l m n:MyNat) : l*(m+n) = l*m + l*n := by
induction n with
|zero => aesop
|succ a ih =>
rewrite [succ_add]
rewrite [mul_succ]
rewrite [mul_succ]
rewrite [ih]
rewrite [add_comm]
rewrite [add_assoc]
conv =>
  lhs
  pattern l*a+l
  rewrite [add_comm]

theorem mul_assoc (l m n:MyNat) : (l*m)*n = l*(m*n) := by
induction n <;> aesop

instance:NatCast MyNat where natCast:=fromNat
def nsmul : Nat -> MyNat -> MyNat :=fun a b => a*b
instance:HMul Nat MyNat MyNat where hMul := nsmul
instance:HPow MyNat Nat MyNat where hPow := fun a b => repeatn a.mul (fromNat b) 1

instance : Lean.Grind.CommSemiring MyNat where
  mul_assoc := mul_assoc
  add_zero := zero_add
  add_comm := add_comm
  add_assoc := add_assoc
  mul_one := mul_one
  one_mul :=  one_mul -- defaultを使いたい
  left_distrib := mul_dist
  right_distrib := by-- defaultを使いたい
  {
    intros a b c
    rewrite [mul_comm,mul_dist,mul_comm]
    conv =>
      pattern c*b
      rewrite [mul_comm]
  }
  zero_mul := mul_zero
  mul_zero := zero_mul-- defaultを使いたい
  mul_comm := mul_comm
  pow_zero := by aesop
  pow_succ := by
  {
    intros a n
    unfold HPow.hPow
    unfold instHPowNat
    simp
    conv =>
      lhs
      unfold fromNat
      simp
    rewrite [mul_comm]
    rfl
  }
  ofNat_succ := by
  {
    intros a
    induction a with
    |zero => aesop
    |succ a ih =>
    simp
    rewrite [ih]
    unfold OfNat.ofNat
    unfold instOfNat
    unfold instOfNatNat
    simp
    conv =>
      lhs
      unfold fromNat
    conv =>
      rhs
      pattern fromNat 1
      unfold fromNat
    rewrite [add_succ]
    have z:fromNat 0 =zero := by aesop
    have zz:fromNat 1 =zero.succ := by aesop
    rewrite [z]
    rewrite [add_zero]
    rewrite [zz]
    aesop
  }
  ofNat_eq_natCast := by aesop
  nsmul_eq_natCast_mul := by aesop

instance : CommSemiring MyNat where
  nsmul := nsmul
  mul_assoc := mul_assoc
  add_zero := zero_add
  zero_add := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_one := mul_one
  mul_zero := zero_mul
  one_mul := one_mul
  left_distrib := mul_dist
  zero_mul := mul_zero
  mul_comm := mul_comm
  right_distrib := by
  {
    intros a b c
    rewrite [mul_comm,mul_dist,mul_comm]
    conv =>
      pattern c*b
      rewrite [mul_comm]
  }
  nsmul_zero := by
  {
    intros x
    unfold nsmul
    unfold Nat.cast
    unfold NatCast.natCast
    unfold instNatCast
    simp
    unfold fromNat
    aesop
  }
  nsmul_succ := by
{
  intros n x
  unfold nsmul
  unfold Nat.cast
  unfold NatCast.natCast
  unfold instNatCast
  simp
  conv =>
    lhs
    unfold fromNat
    unfold HMul.hMul
    unfold instHMul
    unfold Mul.mul
    unfold instMul
    simp
  rewrite [<-succ_mul]
  rfl
}
  natCast_succ := by
{
  intros n
  unfold NatCast.natCast
  unfold instNatCast
  simp
  conv =>
    lhs
    unfold HAdd.hAdd
    unfold instHAdd
    unfold Add.add
    unfold instAddNat
    unfold Nat.add
    unfold fromNat
  have z : 1=zero.succ := by aesop
  rewrite [z]
  rewrite [succ_add]
  aesop
}

example (m n : MyNat) : n * (n + m) = n * n + n * m := by
  -- `ring` が使えるようになった！
  ring

--- 4.順序

@[simp]
def le (n m:MyNat) := exists c, n+c = m
infix:50 " <= " => le

@[aesop unsafe]
theorem le_refl n : n <= n := by aesop

@[aesop unsafe]
theorem le_step (n m:MyNat) : n <= m -> n <= m.succ := by
aesop

theorem le_trans l m n : l <= m -> m <= n -> l <= n := by
intros a b
cases a with | intro c h =>
cases b with | intro d i =>
exists c+d
rewrite [<-add_assoc,h,i]
simp

theorem le_asym n m : le n m -> le m n -> n = m := by
intros a b
cases a with | intro c h =>
cases b with | intro d i =>
rewrite [<-h] at i
rewrite [add_assoc] at i
replace i : c+d=zero := add_elim i
replace i : c = zero := by
  apply add_eq_zero
  rewrite [add_comm]
  apply i
rewrite [i] at h
aesop

theorem le_total n m: (le n m) ∨ (le m n) := by
induction n with
| zero => aesop
| succ a ih => induction m with
  | zero => aesop
  | succ b ij =>
    cases ih with
    |inr ih =>
      right
      apply (le_trans b.succ a a.succ)
      aesop
      apply le_step
      apply le_refl
    |inl ih =>
      unfold le at ih
      cases ih with
      | intro  w h => cases w with
        | zero =>
          rewrite [<-h]
          right
          simp
          exists 1
          have z : 1=zero.succ := by
            aesop
          aesop
        | succ c =>
          left
          unfold le
          exists c
          aesop

@[simp]
def lt (n m:MyNat) := le n m ∧ ¬ n = m
infix:50 " < " => lt

@[aesop safe]
theorem not_eq_succ (m n:MyNat) : ¬ m + n.succ = m := by
induction m with
| zero => aesop
| succ a ih => aesop

theorem lt_le_succ (n m:MyNat) : n<m ↔ n.succ <= m  := by
apply Iff.intro
intros a
cases a with
| intro left right =>
  unfold le at left
  cases left with
  | intro w h => cases w with
    | zero => aesop
    | succ ww =>
      aesop
intros a
unfold le at a
cases a with
| intro w h =>
  rewrite [add_succ] at h
  rewrite [<-succ_add] at h
  unfold lt
  constructor
  aesop
  unfold Not
  intros a
  rewrite [a] at h
  apply (not_eq_succ m w)
  aesop


@[aesop safe]
theorem lt_trans (l m n:MyNat) : l<m -> m<n -> l<n := by
intros a b
have z := (lt_le_succ l m)
have zz := (lt_le_succ m n)
cases z with
| intro mp =>
cases zz with
| intro mpp  =>
replace a := mp a
replace b := mpp b
have z: le m m.succ := by
  apply le_step
  apply le_refl
have zz: le l.succ n := by
  apply (le_trans _ _ _ a ?_)
  apply (le_trans _ _ _ z b)
have y := lt_le_succ l n
aesop

@[aesop unsafe]
theorem mul_elim (n m:MyNat) : zero < n -> n * m = n -> m = 1 := by
intros a b
replace aa := (lt_le_succ zero n).1 a
cases aa with |intro w h
rewrite [<-h] at b
simp at b
cases m with
| zero => aesop
| succ aa =>
have z:w*aa.succ = w+w*aa := by
  simp
rewrite [z] at b
simp at b
rewrite [add_comm] at b
rewrite [add_assoc] at b
have b := add_elim b
have b := add_eq_zero _ _ b
aesop

@[aesop unsafe]
theorem mul_eq_one (n m:MyNat) : n * m = 1 -> n = 1 := by
intros a
cases n with
| zero => aesop
| succ nn => cases m with
  | zero =>
    rewrite [zero_mul]at a
    contradiction
  | succ mm =>
    simp at a
    have a : (nn + mm) + nn * mm = zero := by
      have succ_inj (z zz:MyNat) : z.succ=zz.succ -> z=zz := by aesop
      replace a:= succ_inj _ _ a
      aesop
    rewrite [add_comm] at a
    replace a:=add_eq_zero _ _ a
    rewrite [add_comm] at a
    replace a:=add_eq_zero _ _ a
    aesop

-- 5.整除

@[simp]
def divides (d n:MyNat) := exists k, d * k = n
infix:50(priority:=2000) " ∣ " => divides

theorem zero_divides_only_zero n : zero ∣ n -> n=0 := by
intros a
cases a with
| intro w h
aesop

theorem all_divides_zero d : d ∣ zero := by
simp
exists zero

theorem divides_trans (d n m:MyNat) : d ∣ n -> n ∣ m -> d ∣ m := by
intros a b
simp at a
simp at b
cases a with | intro z zz
cases b with |intro y yy
rewrite [<-zz] at yy
rewrite [mul_assoc] at yy
exists z*y

theorem divides_assym (n m:MyNat) : n ∣ m -> m ∣ n -> n=m := by
intros a b
simp at a
simp at b
cases a with | intro z zz
cases b with |intro y yy
rewrite [<-zz] at yy
rewrite [mul_assoc] at yy
cases n with
|zero => aesop
| succ nn =>
  replace yy := mul_elim _ _ ?_ yy
  replace yy := mul_eq_one _ _ yy
  rewrite [yy] at zz
  have q : 1 = zero.succ := by aesop
  rewrite [q] at zz
  rewrite [mul_one] at zz
  aesop
  aesop


theorem le1 {a b:MyNat}: a+b<=a -> b=0 := by
intros c
unfold le at c
cases c
case intro w h =>
rewrite [add_assoc] at h
replace h := @add_elim _ _ h
rewrite [add_comm] at h
replace h:= add_eq_zero _ _ h
aesop

theorem mul_le {a b c:MyNat} : (a.succ)*b <= (a.succ)*c -> b<=c := by
have t := le_total b c
cases t
{
  case inl h =>
  aesop
}
{
  case inr h =>
  intros d
  unfold le at h
  cases h
  case intro cc eq =>
  rewrite [<-eq] at d
  rewrite [mul_dist] at d
  replace d:=le1 d
  have z : a=a+zero := by
    aesop
  rewrite [z] at d
  rewrite [<-succ_add] at d
  rewrite [mul_comm] at d
  rewrite [mul_dist] at d
  replace d := add_eq_zero _ _ d
  rewrite [mul_one] at d
  rewrite [d] at eq
  aesop
}

theorem divides_elim {a b c d:MyNat} :a+b=c -> d ∣a -> d ∣c ->  d ∣b := by
  intros q w e
  unfold divides at w
  unfold divides at e
  cases w
  case intro w h =>
  cases e
  case intro ww hh =>
  rewrite [<-h] at q
  rewrite [<-hh] at q
  unfold divides
  cases d
  case zero =>
    have z : b=0 := by
      aesop
    exists zero
    aesop
  case succ dd=>
    have z : dd.succ*w <= dd.succ*ww := by
      unfold le
      exists b
    replace z := mul_le z
    unfold le at z
    cases z
    case intro w1 h1 =>
    exists w1
    rewrite [<-h1] at q
    rewrite [mul_dist] at q
    replace q := add_abac.1 q
    aesop

-- 6.剰余

@[simp]
def eq_dec (n m: MyNat) : Bool := match n with
|zero => match m with
  |zero => true
  |succ _ => false
|succ n' => match m with
  |zero => false
  |succ m' => eq_dec n' m'

@[simp]
theorem eq_dec1 (n m: MyNat) : eq_dec n m = true <-> n=m:= by
have h : ∀(a b:MyNat), eq_dec a b = true <-> a=b := by
  intro a
  induction a with
  | zero => aesop
  | succ a' ih => aesop
aesop

instance eq_dec2 (n m:MyNat) : Decidable (n=m) := by
generalize h: eq_dec n m = b
cases b with
| true =>
  apply isTrue
  aesop
| false =>
  apply isFalse
  unfold Not
  intros a
  replace a := (eq_dec1 n m).2 a
  aesop

@[aesop unsafe,simp]
def mod (n m:MyNat) := match n with
| zero => zero
| succ n' => match (eq_dec (mod n' m).succ m) with
| true => zero
| false => (mod n' m).succ
--普通は固定する変数が先だが数学的な慣習に従う
infix:100 " % " => mod

#eval (mod 10 5)
#eval (mod 13 5)
#eval (mod 0 5)
#eval (mod 5 0)

theorem mod_eq (n m:MyNat): ∃ c, (c*m + n%m) = n := by
have b : ∀ n:MyNat, ∃c, (c*m + n%m) = n := by
  intros n
  induction n with
  | zero =>
    exists zero
    simp
  | succ n' ih =>
    unfold mod
    generalize h: (n' % m).succ.eq_dec m = b
    cases b with
    | false =>
      simp
      aesop
    | true =>
      simp
      replace h := (eq_dec1 _ _).1 h
      cases ih with
      | intro c ih =>
        have z : c * m + (n' % m).succ = n'.succ := by
          simp
          aesop
        rw [h] at z
        exists c+zero.succ
        aesop
aesop


theorem mod_lt (n m:MyNat): 0<m -> n%m < m:= by
intros a
replace a := (lt_le_succ _ _).1 a
apply (lt_le_succ _ _).2
induction n with
| zero =>
    aesop
| succ n' ih =>
    unfold mod
    generalize h: (n' % m).succ.eq_dec m = b
    cases b with
    | true =>
      simp
      apply a
    | false =>
      simp
      have z:¬ (n' % m).succ = m := by
        unfold Not
        intros a
        replace a := (eq_dec1 _ _).2 a
        aesop
      have z:(n' % m).succ<m := by aesop
      have z:(n' % m).succ.succ <= m := by
        replace y := lt_le_succ (n' % m).succ m
        aesop
      aesop


-- 7.ユークリッド

theorem mynat_acc (n :MyNat) : Acc lt n := by
induction n with
|zero =>
  apply Acc.intro
  intros y a
  exfalso
  have z : zero<=y:= by
    unfold le
    exists y
  unfold lt at a
  have zz : y=zero :=by
    apply le_asym
    apply a.left
    aesop
  aesop
| succ n' ih=>
  have ih2 := ih
  apply Acc.intro
  intros y a
  cases ih with
  | intro h g=>
    replace a := (lt_le_succ _ _).1 a
    unfold le at a
    cases a with
    | intro w h =>
      cases w with
      | zero =>
        have z : y=n' :=  by aesop
        aesop
      | succ w' =>
        apply g
        apply (lt_le_succ _ _).2
        simp at h
        rewrite [<-add_succ] at h
        unfold le
        exists w'


@[simp]
theorem succ_nat_mynat (n:MyNat) : toNat (n.succ) = (toNat n).succ := by
aesop

@[simp]
theorem succ_mynat_nat (n:Nat) : fromNat (n.succ) = (fromNat n).succ := by
aesop

@[simp]
theorem add_mynat_nat(n m:Nat): fromNat (n+m) = fromNat (n) + fromNat (m):= by
induction m with
| zero =>
  unfold fromNat
  simp
| succ m' ih =>
  simp
  rewrite [<-Nat.add_assoc]
  aesop

@[simp]
theorem add_nat_mynat(n m:MyNat): toNat (n+m) = toNat (n) + toNat (m):= by
induction m with
|zero => aesop
|succ m' ih=> aesop


theorem to_from_nat (n:MyNat) : fromNat n.toNat = n := by
induction n with
| zero => aesop
| succ n' ih => aesop

theorem add_tonat {n m} : toNat (n+m) = n.toNat + m.toNat := by
induction n with
|zero => aesop
|succ n' ih =>
simp
ring

theorem lt_tonat {n m} : n<m -> Nat.lt n.toNat m.toNat := by
intros a
have a := (lt_le_succ _ _).1 a
unfold le at a
cases a with
| intro w h =>
have z : toNat (n.succ+w) = toNat m := by rw [h]
rewrite [add_tonat] at z
rewrite [Nat.lt.eq_1]
rewrite [<-z]
aesop

def gcd (n m:MyNat) :MyNat := by
generalize eq :m=mm
match m with
| zero => exact n
| succ _ => exact gcd m (n%m)
termination_by toNat m
decreasing_by
case _ a =>
rewrite [<-eq]
have z:n%a.succ<a.succ := by
  {
    apply mod_lt
    apply (lt_le_succ _ _).2
    unfold le
    exists a
  }
apply lt_tonat
apply z

#eval (gcd 15 20)
#eval (gcd 8 20)

theorem ind_mynat1 (P:MyNat -> Prop) :
  (forall n, (forall k, k<n -> P k) -> P n) -> (forall n, forall k, k<=n -> P k) := by
{
  intros a n
  induction n with
  |zero =>
  {
    intros k b
    have z : forall k:MyNat,zero <= k := by
      intros k
      unfold le
      exists k
    have zz : k=zero := by
      apply le_asym
      apply b
      apply z k
    apply a
    intros kk aa
    exfalso
    rewrite [zz] at aa
    cases aa
    case zero.a.intro left right =>
      have x : kk=zero:=by
        apply le_asym
        apply left
        apply z kk
      aesop
  }
  |succ b ih =>
  {
    intros kk bb
    have z : forall a b, a<=b -> a=b ∨ a<b:=by
      intros a b h
      unfold le at h
      cases h
      case intro eq c=>
      cases eq
      case zero => aesop
      case succ d=>
        right
        apply (lt_le_succ _ _).2
        unfold le
        rewrite [succ_add] at c
        rewrite [<-add_succ] at c
        exists d
    replace bb := z _ _ bb
    cases bb
    {
    case succ.inl h=>
      apply a
      intros k aa
      apply ih
      rewrite [h] at aa
      replace aaa := (lt_le_succ k b.succ).1 aa
      aesop
    }
    {
      case succ.inr h=>
      apply ih
      unfold le
      replace h := (lt_le_succ _ _ ).1 h
      unfold le at h
      aesop
    }
  }
}

theorem zero_le : forall k:MyNat,zero <= k := by
intros k
unfold le
exists k


theorem ind_mynat (P:MyNat -> Prop) :
  (forall n, (forall k, k<n -> P k) -> P n) -> (forall n, P n) := by
intros h m
{
  have b := ind_mynat1 _ h
  apply b m m
  aesop
}

def posmy := { z // zero < z }

theorem zero0 : zero = 0:=by
aesop

@[aesop unsafe]
theorem succ_le (a:MyNat) : a < a.succ := by
apply (lt_le_succ _ _).2
apply le_refl

@[aesop unsafe]
theorem zero_lt_succ (a:MyNat) : zero < a.succ := by
apply (lt_le_succ _ _).2
unfold le
exists a

theorem gcd_linear : forall b a,exists (p q r s:MyNat), p*a+q*b = (r*a+s*b) + (gcd a b) := by
apply ind_mynat
intros n ih
unfold gcd
intro a
split
exists zero.succ
exists zero
exists zero
exists zero
simp
{
  {
    case h_2 eq aa m =>
    have ih := ih (a%aa.succ) ?_ aa.succ
    {
      rewrite [<-m] at *
      cases mod_eq a eq
      case intro h w =>
      rcases ih with ⟨p',q',r',s',t⟩
      exists q'
      exists p' + s'*h
      exists s'
      exists r'+q'*h
      conv =>
        lhs
        rewrite [<-w]
      conv =>
        rhs
        pattern s'*a
        rewrite [<-w]
      rewrite [mul_dist]
      rewrite [add_comm]
      rewrite [mul_comm]
      rewrite [mul_dist]
      rewrite [<-add_assoc]
      rewrite [mul_comm]
      rewrite [add_assoc]
      rewrite [add_assoc]
      rewrite [add_comm]
      rewrite [add_assoc]
      rewrite [add_assoc]
      rewrite [add_comm] at t
      rewrite [t]
      ring
    }
    apply mod_lt
    apply zero_lt_succ
  }
}

theorem gcd_greatest : forall b,forall a d, d ∣ a -> d ∣ b -> d ∣ (gcd a b) := by
intros a b c d e
have z := gcd_linear a b
rcases d with ⟨dd,ddd⟩
rcases e with ⟨ee,eee⟩
rcases z with ⟨p',q',r',s',t⟩
symm at t
apply divides_elim t
rewrite [<-ddd]
rewrite [<-eee]
unfold divides
exists r'*dd+s'*ee
rewrite [mul_dist]
conv =>
  pattern r'*dd
  rewrite [mul_comm]
rewrite [<-mul_assoc]
rewrite [mul_comm]
apply add_abac.2
conv =>
  pattern c*ee
  rewrite [mul_comm]
rewrite [mul_comm]
rewrite [mul_assoc]
rfl
rewrite [<-ddd]
rewrite [<-eee]
unfold divides
exists p'*dd+q'*ee
ring


theorem mod_le : a < b -> a%b = a := by
{
  induction a with
  |zero => {
    intro aa
    unfold mod
    rfl
  }
  |succ aa ih => {
    intros c
    have z : aa<aa.succ := by
      apply (lt_le_succ _ _).2
      unfold le
      exists zero
      simp
    have z : aa<b := by
      apply lt_trans _ _ _ z c
    replace ih := ih z
    unfold mod
    rewrite [ih]
    split
    {
      case h_1 hea x y =>
      replace d := (eq_dec1 _ _).1 y
      exfalso
      aesop
    }
    {
      case h_2 =>
      simp
    }
  }
}

theorem mod_aa {a} : a%a = zero := by
{
  unfold mod
  split
  {
    case h_1 =>
    rfl
  }
  {
    case h_2 n x=>
    have z : x%x.succ = x := by
      apply mod_le
      apply succ_le
    rewrite [z]
    split
    rfl
    case h_2 heq =>
    exfalso
    have heq2 := (eq_dec1 x.succ x.succ).2
    aesop
  }
}

theorem gcd_aa : forall a:MyNat, gcd a a = a := by
{
  intros a
  unfold gcd
  split
  {
    case h_1 b c =>
    rfl
  }
  {
    case h_2 b c m=>
    rewrite [<-m]
    rewrite [mod_aa]
    unfold gcd
    rfl
  }
}

theorem gcd_divides_a_and_b {a b} : (gcd a b) ∣ a  ∧ gcd a b ∣ b:= by
{
  have q : forall b a, (gcd a b) ∣ a  ∧ gcd a b ∣ b := by
    apply ind_mynat
    intros a b c
    constructor
    unfold gcd
    split
    {
      case h_1 =>
      aesop
    }
    {
      case h_2 eq a m=>
      generalize eq:c%a.succ = z
      have b := b (c%a.succ)
      have d := mod_lt c a.succ ?_
      have b := b d a.succ
      rewrite [eq] at b
      have f := mod_eq c a.succ
      cases f
      {
        case intro h w =>
        rewrite [eq] at w
        cases b
        case intro left right =>
        rewrite [<-w]
        cases left
        case intro ww hh =>
        cases right
        case intro www hhh =>
        conv =>
          rhs
          rewrite [<-hh]
        conv =>
          arg 2
          arg 2
          rewrite [<-hhh]
        unfold divides
        exists h*ww + www
        ring
      }
      {
        case refine_1 =>
        apply (lt_le_succ _ _).2
        unfold le
        exists a
      }
    }
    {
      unfold gcd
      split
      {
        case h_1  eq m=>
        apply all_divides_zero
      }
      {
        case h_2 eq a m=>
        apply (b (c%a.succ) ?_ a.succ).1
        apply mod_lt
        apply (lt_le_succ _ _).2
        unfold le
        exists a
      }
    }
  apply q
}

theorem gcd_unique {a b:MyNat}: forall g1 g2,
  g1 ∣ a ∧ g2 ∣ a ∧ g1 ∣ b ∧ g2 ∣ b ->
  (forall d, d ∣ a ∧ d ∣b -> d ∣ g1) ->
  (forall d, d ∣ a ∧ d ∣b -> d ∣ g2) ->
  g1=g2 := by
intros c d e f g
apply divides_assym
apply g
aesop
apply f
constructor
aesop
aesop

theorem gcd_comm : forall a b, gcd a b = gcd b a:= by
intros a b
wlog h:a<b with H
have z : a=b ∨ b<a := by
  have q := le_total a b
  cases q
  {
    case inl hh =>
    left
    unfold le at hh
    rcases hh with ⟨w,h⟩
    cases w
    case zero => aesop
    case h.intro.succ x s=>
    exfalso
    apply x
    apply (lt_le_succ _ _).2
    aesop
  }
  {
    case inr hh =>
    cases eq_dec2 a b
    {
      case isFalse hhh =>
      right
      unfold lt
      constructor
      aesop
      intros x
      apply hhh
      rw [x]
    }
    {
      case isTrue hhh =>
      left
      apply hhh
    }
  }
cases z
{
  case inr.inl h =>
  rewrite [h]
  rfl
}
{
  case inr.inr h =>
  symm
  apply H b a h
}
conv =>
  lhs
  unfold gcd
split
exfalso
have h := (lt_le_succ a zero).1 h
aesop
case h_2 eq b c=>
have z : a%b.succ = a := by
  apply mod_le h
rewrite [z]
rfl


theorem gcd_assoc a b c : gcd a (gcd b c) = gcd (gcd a b) c:= by
have da := divides_assym (gcd a (gcd b c)) (gcd (gcd a b) c)
have aa : gcd a (gcd b c) ∣ a:= by
  apply (gcd_divides_a_and_b).1
have bb : gcd a (gcd b c) ∣ b:= by
  apply divides_trans _ _ _
  apply gcd_divides_a_and_b.2
  apply gcd_divides_a_and_b.1
have cc : gcd a (gcd b c) ∣ c:= by
  apply divides_trans _ _ _
  apply gcd_divides_a_and_b.2
  apply gcd_divides_a_and_b.2
have aaa : (gcd (gcd a b) c) ∣ a:= by
  apply divides_trans _ _ _
  apply gcd_divides_a_and_b.1
  apply gcd_divides_a_and_b.1
have bbb : (gcd (gcd a b) c) ∣ b:= by
  apply divides_trans _ _ _
  apply gcd_divides_a_and_b.1
  apply gcd_divides_a_and_b.2
have ccc : (gcd (gcd a b) c) ∣ c:= by
  apply gcd_divides_a_and_b.2
have z1 : gcd a (gcd b c) ∣ (gcd (gcd a b) c) := by
  apply gcd_greatest
  apply gcd_greatest
  apply gcd_divides_a_and_b.1
  apply divides_trans
  apply gcd_divides_a_and_b.2
  apply gcd_divides_a_and_b.1
  apply divides_trans
  apply gcd_divides_a_and_b.2
  apply gcd_divides_a_and_b.2
have z2 : gcd (gcd a b) c ∣ gcd a (gcd b c) := by
  apply gcd_greatest
  apply divides_trans
  apply gcd_divides_a_and_b.1
  apply gcd_divides_a_and_b.1
  apply gcd_greatest
  apply divides_trans
  apply gcd_divides_a_and_b.1
  apply gcd_divides_a_and_b.2
  apply gcd_divides_a_and_b.2
apply da z1 z2

-- 8.素数

def is_prime (p:MyNat) : Prop := zero.succ<p ∧ forall k, k ∣p ->  k=zero.succ ∨ k=p

-- 9. 「p|abならばp|aまたはp|b」が目標

theorem pabpapb p a b : is_prime p -> p ∣ a*b -> p ∣a∨p ∣b := by
intros c d
have z:zero<p := by
  unfold is_prime at c
  cases c
  case intro l _ =>
  aesop
have z := gcd_linear a p
rcases z with ⟨pp,q,r,s,t⟩
have y := (@gcd_divides_a_and_b a p).2
unfold is_prime at c
rcases c with ⟨_,kk⟩
have kk := kk (a.gcd p) y
cases kk
{
  case inl h=>
  right
  rewrite [gcd_comm] at t
  rewrite [h] at t
  have mmn : forall m n:MyNat, m=n -> b*m=b*n := by aesop
  have mmn := mmn _ _ t
  cases d
  case intro w h hh hhhh=>
  have zz : zero.succ = 1 := by aesop
  rewrite [zz] at mmn
  have eq:b*(pp*p+q*a)=p*(b*pp)+a*b*q := by ring
  have eq2 : b*(r*p+s*a+1) = p*(b*r) + a*b*s + b := by ring
  rewrite [eq,eq2] at mmn
  rewrite [<-hhhh] at mmn
  apply divides_elim
  symm
  apply mmn
  exists b*r+hh*s
  ring
  exists b*pp+hh*q
  ring
  }
{
  case inr h =>
  left
  have y := (@gcd_divides_a_and_b a p).1
  rw [h] at y
  apply y
}

def le_total_dec n m := match n with
|zero => true
|succ n' => match m with
  |zero => false
  |succ m' => le_total_dec n' m'

theorem le_total_dec1 {n m} : le_total_dec n m = true <-> n <= m := by
have z:forall n, forall m, le_total_dec n m = true <-> n<=m := by
{
  intro n
  induction n with
  | zero =>
  {
    intro a
    constructor
    intros b
    exists a
    intro b
    aesop
  }
  | succ n' ih=>
  {
    intro m
    cases m
    constructor
    intro a
    unfold le_total_dec at a
    aesop
    aesop
    constructor
    {
      case succ.succ.mp a=>
      intros c
      unfold le_total_dec at c
      simp at c
      have z:=(ih _).1 c
      rcases z with ⟨w,h⟩
      exists w
      rewrite [<-h]
      aesop
    }
    {
      case succ.succ.mpr a =>
      intros c
      unfold le_total_dec
      simp
      apply (ih _).2
      aesop
    }
  }
}
apply z
