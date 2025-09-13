import mynat

open MyNat

namespace binom

def frac (n:MyNat) := match n with
| .zero => 1
| .succ n' => n * frac n'

#eval frac 5

theorem divides1 : forall n d, 0<n -> d ∣ n -> d <= n := by
intros n d h1 h2
rcases h2 with ⟨w,h⟩
cases w with
|zero => aesop
| succ w' =>
simp at h
rewrite [<-h]
exists d*w'

theorem frac1 : forall p, is_prime p -> forall k, k<p -> ¬ p ∣ frac k := by
intros p hp k
induction k with
| zero =>
intros a
unfold Not
intros b
unfold frac at b
rcases b with ⟨w,ww⟩
have ww := mul_eq_one p w ww
unfold is_prime at hp
rcases hp with ⟨⟨l1,l2⟩ ,_ ⟩
apply l2
aesop
| succ k' ih=>
intros a b
unfold frac at b
have bb := pabpapb p _ _ hp b
cases bb with
| inl h=>
have hh := divides1 _ _ ?_ h
have hhh:k'.succ = p := by
  apply le_asym
  apply a.1
  apply hh
aesop
apply lt_le_succ.2
exists k'
|inr h =>
apply ih
apply MyNat.lt_trans
have z : k'<k'.succ := by
  apply lt_le_succ.2
  exists 0
  simp
apply z
apply a
apply h

def binom (n k:MyNat) :MyNat := match n with
| .zero => match k with
  | .zero => 1
  | .succ _ => 0
| .succ n' => match k with
  | .zero => 1
  | .succ k' => (binom n' k') + (binom n' k)

#eval binom 1 0
#eval binom 1 1
#eval binom 2 0
#eval binom 2 1
#eval binom 2 2
#eval binom 3 0
#eval binom 3 1
#eval binom 3 2
#eval binom 3 3
#eval binom 3 4

theorem binom1 : forall n, binom n n = 1 ∧ forall k,binom n (n+k+1) = 0 := by
intros n
induction n with
|zero =>
constructor
aesop
intros k
simp
have a : k+1=k.succ := by aesop
rewrite [a]
unfold binom
rewrite [<-zero0]
simp
|succ n' ih =>
constructor
unfold binom
simp
rewrite [ih.1]
have q := ih.2 0
simp at q
rewrite [q]
aesop
intros k
rewrite [add_succ]
rewrite [add_succ]
unfold binom
simp
have q := ih.2 k
have q1 := ih.2 (k+1)
ring_nf at *
aesop

theorem binom_frac :forall n k c,  n=k+c -> (binom n k)*(frac k)*(frac c)=(frac n) := by
intro n
induction n with
|zero =>
intros a c h
symm at h
have hh := add_eq_zero h
aesop
|succ n' ih =>
intros k c eq
unfold binom
split
{
  simp at eq
  rewrite [<-eq]
  simp
  conv =>
    pattern frac 0
    unfold frac
  split
  aesop
  case h_2 heq =>
  injection heq
}
{
  case h_2 a b =>
  rewrite [add_succ] at eq
  injection eq with eq
  have ihb := ih b c eq
  rewrite [mul_assoc,mul_comm,mul_dist]
  conv =>
    pattern frac b.succ
    unfold frac
  cases c with
  |zero =>
    simp at eq
    rewrite [eq]
    rewrite [(binom1 b).1]
    have z :=(binom1 b).2 0
    simp
    ring_nf at *
    rewrite [z]
    simp
    have w : frac 0 = 1 := by aesop
    rewrite [w]
    conv =>
      rhs
      rewrite [<-succ_add_one]
      unfold frac
    rewrite [succ_add_one]
    ring
  |succ c' =>
    have ihc' := ih b.succ c' ?_
    have z: b.succ * frac b * frac c'.succ * binom n' b + frac b.succ * frac c'.succ * binom n' b.succ
            = binom n' b * frac b * frac c'.succ * b.succ + binom n' b.succ * frac b.succ * frac c' * c'.succ := by
      conv =>
        lhs
        arg 2
        pattern frac c'.succ
        unfold frac
      ring
    rewrite [z,ihb,ihc']
    rewrite [<-mul_dist]
    conv =>
      rhs
      unfold frac
      arg 1
      rewrite [eq]
    simp
    ring
    simp at *
    rewrite [eq]
    ring
}

theorem binom_frac2 :forall n k,  k<=n -> exists c, n=k+c ∧  (binom n k)*(frac k)*(frac c)=(frac n) := by
intros n k kn
rcases kn with ⟨w,h⟩
exists w
constructor
rw [h]
apply binom_frac
rewrite [h]
rfl

theorem binom_prime : forall p, is_prime p -> forall k, 0<k -> k<p ->
  p ∣ binom p k := by
intros p hp k k1 k2
have a := binom_frac2 p k ?_
{
rcases a with ⟨w,⟨eq1,eq2⟩ ⟩
have z : p ∣ frac p := by
  unfold frac
  split
  rcases hp with ⟨t,tt⟩
  have t := lt_le_succ.1 t
  have t := le_asym _ _ t ?_
  injection t
  exists 2
  case h_2 t =>
  exists frac t
rewrite [<-eq2] at z
have zz := pabpapb _ _ _ hp z
cases zz with
| inl h =>
{
  have zz := pabpapb _ _ _ hp h
  cases zz with
  | inl hh =>
  aesop
  |inr hh =>
  exfalso
  have q:= frac1 p hp k k2 hh
  apply q
}
| inr h =>
{
  exfalso
  apply frac1 p hp _ ?_ h
  apply lt_le_succ.2
  cases k with
  | zero =>
    {
      unfold lt at k1
      aesop
    }
  | succ k' =>
    rewrite [eq1]
    exists k'
    simp
    ring
}
}
have k2 := lt_le_succ.1 k2
apply le_trans _ k2
apply le_step
apply @MyNat.le_refl k

@[simp]
def pow a n := repeatn (fun x => a*x) n 1

#eval pow 2 3
#eval pow 3 0
#eval pow 0 0
#eval pow 0 1

theorem pow1 : pow a (n+m) = pow a n * pow a m := by
induction m with
|zero =>
simp
|succ m' ih =>
rewrite [succ_add]
simp
rewrite [<-pow]
rewrite [<-pow]
rewrite [<-pow]
rewrite [ih]
ring

theorem pow2 : pow a (n*m) = pow (pow a n) m := by
induction m with
|zero => aesop
|succ m' ih =>
rewrite [succ_add_one]
rewrite [mul_dist]
rewrite [pow1]
rewrite [pow1]
rewrite [ih]
rewrite [mul_one]
have z : 1=zero.succ:= by aesop
rewrite [z]
conv =>
  rhs
  arg 2
  simp
  rewrite [<-pow]

theorem pow3 : pow (a*b) n = pow a n * pow b n:= by
induction n with
|zero =>
simp
|succ n' ih =>
simp
rewrite [<-pow]
rewrite [<-pow]
rewrite [<-pow]
rewrite [ih]
ring

def accumulate (f:MyNat->MyNat) n := match n with
|zero => f 0
| succ n' => f n + accumulate f n'

theorem accum1 f g n : accumulate (fun z => f z + g z) n = accumulate f n + accumulate g n := by
induction n with
|zero =>
unfold accumulate
rfl
|succ n' ih =>
unfold accumulate
rewrite [ih]
ring

theorem accum2 f n : accumulate f n.succ = (f 0) + accumulate (fun z => f (z+1)) n := by
induction n with
|zero =>
unfold accumulate
unfold accumulate
simp
|succ n' ih =>
unfold accumulate
rewrite [ih]
rewrite [succ_add_one]
rewrite [succ_add_one]
ring

theorem accum3 f a n : accumulate (fun z => a * f z) n = a * accumulate f n := by
induction n with
|zero =>
unfold accumulate
rfl
|succ n' ih =>
unfold accumulate
rewrite [ih]
ring

theorem pow4 : pow (a+1) n =
  accumulate (fun z => binom n z * pow a z) n := by
induction n with
|zero =>
simp
unfold accumulate
split
case h_1 heq =>
  have z : 1 = zero.succ := by aesop
  injection heq
case h_2 n' heq=>
  unfold binom
  have z : 0=zero :=by aesop
  have zz : 1=zero.succ :=by simp
  rewrite [z]
  simp
  rewrite [zz]
  simp
  exfalso
  injection heq
|succ n' ih =>
  conv =>
    lhs
    unfold pow
    unfold repeatn
    rewrite [<-pow]
    rewrite [ih]
    rewrite [mul_comm]
    rewrite [mul_dist]
    rewrite [mul_one]
  conv =>
    rhs
    rewrite [accum2]
    arg 2
    arg 1
    ext
    unfold binom
    rewrite [<-succ_add_one]
    simp
    rewrite [<-pow]
    rewrite [mul_comm]
    rewrite [mul_dist]
  conv =>
    rhs
    rewrite [accum1]
    arg 2
    arg 1
    arg 1
    ext
    rewrite [mul_assoc]
  conv =>
    rhs
    arg 2
    arg 1
    rewrite [accum3]
    arg 2
    arg 2
    simp
  conv =>
    rhs
    rewrite [add_comm]
    arg 1
    arg 1
    rewrite [mul_comm]
    arg 1
    arg 1
    ext x
    rewrite [mul_comm]
  rewrite [add_assoc]
  apply add_abac.2
  have z : forall x, a*pow a x = pow a (x+1) := by
    intros x
    rewrite [<-zerosucc]
    rewrite [succ_add]
    conv =>
      rhs
      unfold pow
      simp
      rewrite [<-pow]
  conv =>
    rhs
    arg 1
    arg 1
    ext x
    rewrite [z]
  have z : binom n'.succ 0=binom n' 0 := by
    unfold binom
    rewrite [<-zero0]
    simp
    cases n' <;> simp
  rewrite [z]
  conv =>
    arg 2
    arg 2
    rewrite [mul_comm]
  rewrite [add_comm]
  have a2 := accum2 (fun x => pow a x * binom n' x) n'
  rewrite [<-a2]
  conv =>
    rhs
    unfold accumulate
  have z : binom n' n'.succ = 0:=by
    have zz:=(binom1 n').2 0
    simp
    ring_nf at zz
    ring_nf
    apply zz
  rewrite [z]
  rewrite [zero_mul,add_zero]
  conv =>
    rhs
    arg 1
    ext x
    rewrite [mul_comm]
