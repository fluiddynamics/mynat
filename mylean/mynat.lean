import Aesop

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

infix:65 " + " => add
infix:70 " * " => mul

#eval ((3:MyNat) + (4:MyNat))
#eval ((3:MyNat) * (4:MyNat))

-- 3. 定理の証明

@[aesop safe,simp]
theorem add_zero (n : MyNat) : zero + n = n:= by aesop
@[aesop safe,simp]
theorem zero_add (n:MyNat) : n + zero = n := by
induction n with
| zero => aesop
| succ =>unfold add;aesop

@[aesop safe,simp]
theorem add_succ (n m:MyNat) : n.succ + m = (n+m).succ := by
aesop

@[aesop safe,simp]
theorem succ_add (n m:MyNat) : n + m.succ = (n+m).succ := by
induction n <;> aesop

--a+b = b+a
@[aesop unsafe,simp]
theorem add_comm (m n : MyNat) : n+m = m+n := by
induction n <;> aesop

@[aesop unsafe,simp]
theorem add_assoc (l m n:MyNat) : l+(m +n) = (l + m) + n := by
induction n <;> aesop

@[aesop unsafe]
theorem add_elim {n} {m} : n + m = n -> m = zero := by
induction n <;> aesop

@[aesop safe]
theorem add_eq_zero n m : n+m=zero -> m=zero := by
induction n <;> aesop

theorem add_abac {a b c} : a+b=a+c <-> b=c := by
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
| succ m' ih => unfold mul;aesop

@[simp]
theorem one_mul (m:MyNat) : zero.succ * m = m := by
induction m with
| zero => aesop
| succ m' ih =>unfold mul;aesop

@[aesop safe,simp]
theorem mul_succ (m n:MyNat) : m*(n.succ) = m + m*n := by
aesop

@[simp]
theorem succ_mul (m n:MyNat) : (m.succ)*n = n + m*n := by
induction n <;> aesop

--a*b = b*a
theorem mul_comm (m n : MyNat) : n*m = m*n := by
induction n <;> aesop

@[simp]
theorem mul_dist (l m n:MyNat) : l*(m+n) = l*m + l*n := by
induction n <;> aesop

theorem mul_assoc (l m n:MyNat) : l*(m*n) = (l*m)*n := by
induction n <;> aesop

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
rewrite [add_assoc,h,i]
simp

theorem le_asym n m : le n m -> le m n -> n = m := by
intros a b
cases a with | intro c h =>
cases b with | intro d i =>
rewrite [<-h] at i
rewrite [<-add_assoc] at i
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
simp at aa
cases aa with |intro w h
rewrite [<-h] at b
simp at b
cases m with
| zero => aesop
| succ aa =>
have aasucc : aa.succ = aa + zero.succ := by
  aesop
rewrite [aasucc] at b
simp at b
rewrite [<-add_assoc] at b
replace b := add_elim b
rewrite [add_comm] at b
replace b := add_eq_zero _ _ b
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
infix:50 " ∣ " => divides

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
rewrite [<-mul_assoc] at yy
exists z*y

theorem divides_assym (n m:MyNat) : n∣m -> m∣n -> n=m := by
intros a b
simp at a
simp at b
cases a with | intro z zz
cases b with |intro y yy
rewrite [<-zz] at yy
rewrite [<-mul_assoc] at yy
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
rewrite [<-add_assoc] at h
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

theorem divides_elim {a b c d:MyNat} :a+b=c -> d∣a -> d∣c ->  d∣b := by
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

-- TODO: mod_eqで余りが0だととdividesになるという関係（自明か）

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


theorem le_nat_mynat {n m:MyNat}:n<=m <-> (toNat n) <= (toNat m):= by
apply Iff.intro
aesop
intros a
replace a:= Nat.le.dest a
cases a with
|intro w h =>
replace h: fromNat (n.toNat + w) = fromNat m.toNat := by aesop
rewrite [add_mynat_nat] at h
rewrite [to_from_nat] at h
rewrite [to_from_nat] at h
aesop

theorem lt_nat_mynat {n m:MyNat}:n<m <-> (toNat n) < (toNat m):= by
apply Iff.intro
intros a
replace a := (lt_le_succ _ _).1 a
replace a := le_nat_mynat.1 a
apply Nat.add_one_le_of_lt
apply Nat.lt_of_add_one_le
rewrite [succ_nat_mynat] at a
rewrite [Nat.add_one]
aesop
intros a
apply (lt_le_succ _ _).2
apply le_nat_mynat.2
aesop

def gcd (n:MyNat) (m:{z:MyNat // zero<z }) :MyNat := by
generalize h : n%m = a
match a with
| zero   => exact m.val
| succ b => exact gcd m ⟨n%m, by aesop⟩
termination_by toNat m
decreasing_by
  apply lt_nat_mynat.1
  apply mod_lt
  have mp := m.property
  have z : zero=0 := by aesop
  rewrite [<-z]
  aesop

#eval (gcd 15 ⟨20,by
have a:20=succ 19 := by aesop
rewrite [a]
aesop⟩)
#eval (gcd 8 ⟨20,by
have a:20=succ 19 := by aesop
rewrite [a]
aesop⟩)

def euclid (n:MyNat) (m:{z:MyNat // zero<z }) :List MyNat := by
generalize h : n%m = a
match a with
| zero   => exact [m.val]
| succ b => exact m.val :: euclid m ⟨n%m, by aesop⟩
termination_by toNat m
decreasing_by
  apply lt_nat_mynat.1
  apply mod_lt
  have mp := m.property
  have z : zero=0 := by aesop
  rewrite [<-z]
  aesop

#eval (euclid 15 ⟨20,by
have a:20=succ 19 := by aesop
rewrite [a]
aesop⟩)
#eval (euclid 34 ⟨21,by
have a:21=succ 20 := by aesop
rewrite [a]
aesop⟩)

theorem euclid_1 {n m} : exists l ls, euclid n m = List.cons l ls:= by
generalize h : n%m = a
match a with
| zero   =>
exists m.val
exists []
unfold euclid
aesop
| succ k =>
exists m.val
unfold euclid
exists euclid m ⟨n%m, by aesop⟩
split
aesop
aesop

@[aesop safe]
theorem euclid_ne_nil : Not (euclid n m = []) := by
unfold Not
intros a
replace b := @euclid_1 n m
cases b with
|intro w h => cases h with
|intro ww hh =>
rewrite [a] at hh
aesop

theorem getl : forall a:MyNat, [a].getLast? = some a := by aesop

theorem getla : t ≠ [] -> (h::t).getLast? = t.getLast? := by
{
  induction t with
  |nil => aesop
  |cons tail a tail_ih=>
    intros b
    unfold List.getLast?
    simp
}

theorem getlas (ls:List MyNat) (h:ls ≠ []) : ls.getLast? = some (ls.getLast h) := by
induction ls with
|nil => aesop
|cons hh t ih=>
unfold List.getLast?
split
{
case h_1 heq=> aesop
}
{
  case h_2 heq=>
  injection heq with h_Eq tail_eq
  rewrite [<-tail_eq]
  aesop
}

theorem gcd_euclid : gcd n m = (euclid n m).getLast
 (by apply euclid_ne_nil) := by
have z:forall ls a b, ls = euclid a b -> ls.getLast? = some (gcd a b) := by
{
  intros ls
  induction ls with
  |nil =>
  {
    intros a b h
    exfalso
    symm at h
    apply euclid_ne_nil h
  }
  |cons head tail ih=>
  {
    intros a b h
    unfold euclid at h
    unfold gcd
    split at *
    {
    case h_1 z x=>
      split
      rewrite [h]
      apply getl
      case h_2 zz=>aesop
    }
    {
    case h_2 jj jjj=>
      injection h with head_eq tail_eq
      replace ih := ih _ _ tail_eq
      split
      case h_1 hh hhh=>
        exfalso
        aesop
      case h_2 hh hhh =>
        rewrite [<-ih]
        apply getla
        aesop
    }
  }
}
replace z := z (n.euclid m) n m
symm
have zz : n.euclid m = n.euclid m := by aesop
replace z := z zz
replace y := getlas (n.euclid m) (euclid_ne_nil)
rewrite [z] at y
injection y with val_eq
aesop


-- Mathlib/Data/List/Defs.lean参照
@[simp]
def Forall (p : α → Prop) : List α → Prop
  | [] => True
  | x :: l => p x ∧ Forall p l

theorem Forall_1 {P Q:α → Prop}: (forall e, P e -> Q e) -> forall l, Forall P l -> Forall Q l := by
intros a
intros l
induction l with
| nil => aesop
| cons x z ih=>
  intros b
  unfold Forall at b
  unfold Forall
  rcases b with ⟨p, q⟩
  constructor
  apply a
  apply p
  apply ih
  apply q

theorem Forall_2 (P:MyNat -> Prop) ls (h:ls ≠ []): Forall P ls -> P (List.getLast ls h):= by
induction ls with
|nil =>
exfalso
aesop
|cons hh t ih =>
intros a
unfold Forall at a
unfold List.getLast
split
{
  exfalso
  aesop
}
{
  case h_2 heq heq2 b c =>
  injection b with head_eq tail_eq
  aesop
}
{
  case h_3 heq heq2 x as q qq=>
  injection q with head_eq tail_eq
  have z : P (t.getLast (by aesop)) := by
    apply ih
    aesop
  have y : t.getLast (by aesop) = (heq2::x).getLast (by aesop) := by
    aesop
  rewrite [<-y]
  apply z
}


theorem bezout (ls:List MyNat) :
  forall a :MyNat, forall b:{z:MyNat // zero<z },
    ls = euclid a b ->
      Forall (fun e:MyNat => exists (p q r s:MyNat),
        p*a + q*b = (r*a+s*b) + e) ls := by
induction ls with
| nil => {
  intros a b c
  exfalso
  replace x := @euclid_1 a b
  cases x with
  | intro w h => cases h with
  | intro ww hh => aesop
}
| cons head tail ih =>
intros aa bb cc
unfold euclid at cc
split at cc
case _ _ =>
  have s : tail = [] := by aesop
  {
  have ss : head = bb.val := by aesop
  rewrite [s]
  rewrite [ss]
  simp
  exists zero
  exists zero.succ
  exists zero
  exists zero
  simp }
case h_2 heq eq2 _ _ h hh=>
  injection cc with head_eq tail_eq
  replace ih := ih _ _ tail_eq
  cases mod_eq aa bb.val with|intro w h =>
  rewrite [<-h]
  unfold Forall
  constructor
  rewrite [head_eq]
  unfold Forall at ih
  split at ih
  {
  exfalso
  symm at tail_eq
  apply euclid_ne_nil tail_eq
  }
  {
    exists zero
    exists zero.succ
    exists zero
    exists zero
    aesop
  }
  have z: forall e,(∃ p q r s, p * bb + q * aa % bb = (r * bb + s * aa % bb) + e) ->
                    ∃ p q r s, p * (w * bb + aa % bb) + q * bb = (r * (w * bb + aa % bb) + s * bb) + e := by
    intros e a
    rcases a with ⟨p, q, r, s, h_prop⟩
    exists q
    exists p+s*w
    exists s
    exists r+q*w
    have z1 : q * (w * bb.val + aa % bb.val) + (p + s * w) * bb.val = (p*bb.val + q *aa%bb.val) + (q*w +s*w)*bb.val
             := by
      rewrite [mul_dist]
      rewrite [add_comm]
      rewrite [mul_comm]
      rewrite [mul_dist]
      rewrite [add_comm]
      rewrite [add_assoc]
      rewrite [add_comm]
      symm
      rewrite [add_comm]
      rewrite [mul_comm]
      rewrite [mul_dist]
      rewrite [<-add_assoc]
      rewrite [add_comm]
      rewrite [<-add_assoc]
      apply add_abac.2
      rewrite [add_comm]
      symm
      rewrite [<-add_assoc]
      rewrite [mul_assoc]
      rewrite [mul_comm]
      apply add_abac.2
      rewrite [add_comm]
      rw [mul_comm]
    rewrite [z1]
    rewrite [h_prop]
    rewrite [<-add_assoc]
    rewrite [<-add_assoc]
    symm
    rewrite [<-add_assoc]
    rewrite [add_comm]
    rewrite [mul_comm]
    rewrite [mul_dist]
    rewrite [<-add_assoc]
    rewrite [<-add_assoc]
    rewrite [mul_comm]
    apply add_abac.2
    symm
    rewrite [add_comm]
    rewrite [<-add_assoc]
    rewrite [add_comm]
    rewrite [mul_comm]
    rewrite [mul_dist]
    rewrite [<-add_assoc]
    rewrite [<-add_assoc]
    apply add_abac.2
    rewrite [add_assoc]
    rewrite [add_comm]
    apply add_abac.2
    symm
    rewrite [mul_dist]
    rewrite [mul_assoc]
    rewrite [mul_comm]
    apply add_abac.2
    rfl
  apply Forall_1
  apply z
  apply ih

theorem gcd_linear a (b:{z:MyNat // zero<z }) : exists (p q r s:MyNat),
  p*a+q*b = (r*a+s*b) + (gcd a b) := by
have c := bezout (euclid a b) a b (by aesop)
replace c:= Forall_2 _ (euclid a b) euclid_ne_nil c
rewrite [gcd_euclid]
aesop

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

theorem comdiv_gcd : forall b,forall a d, d ∣ a -> d ∣ b.val -> d ∣ (gcd a b) := by
{
  generalize eq : (fun x => forall d a, forall (p:zero<x),d ∣ a -> d ∣ x -> d ∣ (gcd a ⟨x,p⟩)) = P
  have ind := ind_mynat P
  have ind1 : ∀ (n : MyNat), (∀ (k : MyNat), k < n → P k) -> P n:= by
    intros n a
    rewrite [<-eq]
    have z : ∀ (d a : MyNat) (p : zero < n), d ∣ a → d ∣ n → d ∣ a.gcd ⟨n, p⟩ := by
      unfold gcd
      intros h1 h2 h3 h4 h5
      split
      {
        case h_1 j1 j2 j3 j4 =>
        apply h5
      }
      {
        case h_2 j1 j2 j3 j4 j5 j6=>
        have d1 : h1 ∣ h2%n := by
          replace me := mod_eq h2 n
          cases me
          case intro meq mec=>
          have e2 : h1∣meq*n := by
            unfold divides at h5
            cases h5
            case intro h5c h5eq =>
            rewrite [<-h5eq]
            rewrite [mul_comm]
            rewrite [<-mul_assoc]
            simp
          apply divides_elim mec
          apply e2
          apply h4
        have p1 : P (h2%n) := by
          apply a
          apply mod_lt
          rewrite [zero0] at h3
          apply h3
        rewrite [<-eq] at p1
        replace p1 := p1 h1 n
        have p2:zero<h2%n :=by
          {
          rewrite [j4]
          apply (lt_le_succ zero j3.succ).2
          unfold le
          exists j3
          }
        apply p1 p2 h5 d1
      }
    apply z
  replace ind1 := ind_mynat P ind1
  rewrite [<-eq] at ind1
  intro b
  replace ind1 := ind1 b
  change (∀ (d a : MyNat) (p : zero < b.val), d ∣ a → d ∣ b.val → d ∣ a.gcd ⟨b.val, p⟩) at ind1
  intro a d
  replace ind1 := ind1 d a b.property
  apply ind1
}

theorem succ_le (a:MyNat) : a < a.succ := by
apply (lt_le_succ _ _).2
apply le_refl

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

theorem mod_aa : forall a:{z : MyNat // zero<z}, a%a = zero := by
{
  intros a
  cases a.val
  simp
  case succ b =>
  have z : b%b.succ = b := by
    apply mod_le
    apply succ_le
  unfold mod
  rewrite [z]
  have xx : forall p:MyNat, p=p := by aesop
  have x := (eq_dec1 b.succ b.succ).2 (xx _)
  rewrite [x]
  simp
}

theorem gcd_aa : forall a:{z : MyNat // zero<z}, gcd a a = a := by
{
  intros a
  unfold gcd
  have eq := mod_aa a
  split
  rfl
  case h_2 h hh b bb=>
  have zz := mod_aa a
  rewrite [zz] at hh
  exfalso
  aesop
}

theorem gcd_comm : forall a b:{z : MyNat // zero<z}, gcd a b = gcd b a:= by
{
  have d : forall c d:{z : MyNat // zero<z}, c<=d -> gcd c d = gcd d c := by
    intros c d h
    by_cases hh: c=d
    rewrite [hh]
    rewrite [gcd_aa]
    rfl
    have z : c<d := by
      unfold lt
      constructor
      apply h
      unfold Not
      intros x
      unfold Not at hh
      apply hh
      aesop
    have z := mod_le z
    unfold gcd
    split
    {
      case h_1 l _ _ ll _ _=>
      rewrite [z] at ll
      exfalso
      have z := c.property
      rewrite [ll] at z
      aesop
    }
    {
      case h_2 v s _ _=>
      conv =>
        lhs
        unfold gcd
      simp
      have vvv:zero<c%d := by
        rewrite [s]
        aesop
      conv =>
        lhs
        pattern (gcd _)
        rewrite [z]
      conv =>
        lhs
        pattern (c%d)
        rewrite [z]
      conv =>
        lhs
        pattern (c%d)
        rewrite [z]
      split
      aesop
      case h_2 b heq _ _ =>
      conv at heq =>
        lhs
        pattern (c%d)
        rewrite [z]
      split
      {
        case h_1 heq2 _ _ =>
        rewrite [heq2] at heq
        exfalso
        simp at heq
      }
      {
        case h_2 =>
        simp
      }
    }
  intros a b
  have tot := le_total a b
  cases tot
  {
    case inl h=>
    apply d _ _ h
  }
  {
    case inr h =>
    have d:= d b a h
    symm
    apply d
  }
}

theorem gcd_divides_a_and_b : forall b, forall a, (gcd a b) ∣ a  ∧ gcd a b ∣ b:= by
{
  have l1 : forall b, forall z:zero<b, forall a, gcd a ⟨b,z⟩ ∣ a ∧ gcd a ⟨b,z⟩ ∣ b:= by
    apply ind_mynat
    intros c d e f
    unfold gcd
    split
    {
      case h_1 h _=>
      have meq := mod_eq f c
      cases meq
      case intro w meq_p=>
      rewrite [h] at meq_p
      simp at meq_p
      unfold divides
      constructor
      exists w
      rw [mul_comm]
      rw [meq_p]
      exists zero.succ
      aesop
    }
    {
      case h_2 a h b h _ _=>
      have hz : 0<c := by
        rewrite [<-zero0]
        apply e
      have fcz : zero<f%c := by aesop
      have d := d (f%c) (mod_lt f c hz) fcz c
      cases d
      case intro left right =>
      constructor
      {
        have meq := mod_eq f c
        cases meq
        case intro cc ccc  =>
        generalize hh : c.gcd ⟨f % c, fcz⟩ = g
        rewrite [hh] at left
        rewrite [hh] at right
        unfold divides at right
        unfold divides at left
        cases right
        case intro rk rp =>
        cases left
        case intro lk lp =>
        unfold divides
        rewrite [<-ccc]
        rewrite [<-rp]
        rewrite [<-lp]
        exists cc*lk+rk
        rewrite [mul_dist]
        rewrite [mul_comm]
        rewrite [<-mul_assoc]
        conv =>
          lhs
          pattern (lk*g)
          rewrite [mul_comm]
      }
      {
        apply left
      }
    }
  intros
  apply l1
}

def MyPos := {z : MyNat // zero<z}
@[simp]
def divides' (d n:MyPos) := exists k, d.val * k = n.val
infix:50 " ∣ " => divides'

def gcd' (a b:MyPos) :MyPos :=  ⟨gcd a.val b, by
{
  unfold lt
  constructor
  aesop
  unfold Not
  intros h
  have z := (gcd_divides_a_and_b b a.val).left
  rewrite [<-h] at z
  have x := zero_divides_only_zero a.val z
  have xx := a.property
  rewrite [x] at xx
  rewrite [zero0] at xx
  aesop
}⟩

theorem gcd_assoc (a b c:MyPos) : gcd' a (gcd' b c) = gcd' (gcd' a b) c:= by
have da := divides_assym (gcd' a (gcd' b c)).val (gcd' (gcd' a b) c).val
have aa : gcd' a (gcd' b c) ∣ a:= by
  apply (gcd_divides_a_and_b _ _).1
have bb : gcd' a (gcd' b c) ∣ b:= by
  have l1 := (gcd_divides_a_and_b (gcd' b c) a.val).2
  apply divides_trans
  apply l1
  apply (gcd_divides_a_and_b c b.val).1
have cc : gcd' a (gcd' b c) ∣ c:= by
  have l1 := (gcd_divides_a_and_b (gcd' b c) a.val).2
  apply divides_trans
  apply l1
  apply (gcd_divides_a_and_b c b.val).2
have aaa : (gcd' (gcd' a b) c) ∣ a:= by
  have l1 := (gcd_divides_a_and_b (gcd' a b) c.val).2
  apply divides_trans
  apply (gcd_divides_a_and_b _ _).1
  apply (gcd_divides_a_and_b b a.val).1
have bbb : (gcd' (gcd' a b) c) ∣ b:= by
  have l1 := (gcd_divides_a_and_b (gcd' a b) c.val).2
  apply divides_trans
  apply (gcd_divides_a_and_b _ _).1
  apply (gcd_divides_a_and_b b a.val).2
have ccc : (gcd' (gcd' a b) c) ∣ c:= by
    apply (gcd_divides_a_and_b _ _).2
have z1 : (gcd' a (gcd' b c)).val ∣ (gcd' (gcd' a b) c).val := by
  apply comdiv_gcd
  apply comdiv_gcd
  apply (gcd_divides_a_and_b _ _).1
  apply divides_trans
  apply (gcd_divides_a_and_b _ _).2
  apply (gcd_divides_a_and_b _ _).1
  apply divides_trans
  apply (gcd_divides_a_and_b _ _).2
  apply (gcd_divides_a_and_b _ _).2
have z2 : (gcd' (gcd' a b) c).val ∣ (gcd' a (gcd' b c)).val := by
  apply comdiv_gcd
  apply divides_trans
  apply (gcd_divides_a_and_b _ _).1
  apply (gcd_divides_a_and_b _ _).1
  apply comdiv_gcd
  apply divides_trans
  apply (gcd_divides_a_and_b _ _).1
  apply (gcd_divides_a_and_b _ _).2
  apply (gcd_divides_a_and_b _ _).2
have da1 := da z1 z2
apply Subtype.ext da1

-- 8.素数

def is_prime (p:MyNat) : Prop := zero.succ<p ∧ forall k, k∣p ->  k=zero.succ ∨ k=p

-- 9. 「p|abならばp|aまたはp|b」が目標

theorem pabpapb p a b : is_prime p -> p∣a*b -> p∣a∨p∣b := by
intros c d
have z:zero<p := by
  unfold is_prime at c
  cases c
  case intro l _ =>
  aesop
have z := gcd_linear a ⟨p,z⟩
rcases z with ⟨pp,q,r,s,t⟩
have y := (gcd_divides_a_and_b ⟨p,z⟩ a).2
unfold is_prime at c
rcases c with ⟨_,kk⟩
have kk := kk (a.gcd ⟨p, z⟩) y
cases kk
{
  case inl h=>
  right
  rewrite [h] at t
  have mmn : forall m n:MyNat, m=n -> m*b=n*b := by aesop
  have mmn := mmn _ _ t
  cases d
  case intro w h =>
  have m := mmn
  rewrite [mul_comm] at m
  rewrite [mul_dist] at m
  rewrite [mul_comm] at m
  rewrite [<-mul_assoc] at m
  rewrite [mul_comm] at m
  rewrite [<-h] at m
  rewrite [<-mul_assoc] at m
  rewrite [add_comm] at m
  rewrite [mul_assoc] at m
  rewrite [mul_comm] at m
  rewrite [<-mul_dist] at m
  symm at m
  rewrite [mul_comm] at m
  rewrite [mul_dist] at m
  rewrite [mul_dist] at m
  rewrite [mul_comm] at m
  rewrite [<-mul_assoc] at m
  rewrite [<-h] at m
  rewrite [mul_comm] at m
  rewrite [<-mul_assoc] at m
  rewrite [add_comm] at m
  rewrite [add_assoc] at m
  rewrite [add_comm] at m
  rewrite [mul_assoc] at m
  rewrite [mul_comm] at m
  rewrite [add_assoc] at m
  rewrite [add_comm] at m
  rewrite [add_assoc] at m
  rewrite [<-mul_dist] at m
  have q1:b*zero.succ=b := by aesop
  rewrite[q1] at m
  apply divides_elim
  apply m
  exists w*r+b*s
  exists b*q+w*pp
}
{
  case inr h =>
  left
  have y := (gcd_divides_a_and_b ⟨p,z⟩ a).1
  rw [h] at y
  apply y
}
