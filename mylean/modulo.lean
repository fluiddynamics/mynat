import mynat
import binom
open MyNat

namespace modulo

variable (m : MyNat)

def modeq (a b:MyNat) := mod a m = mod b m

local infix:50 " ≡ " => modeq m

-- 同値関係であることを示しておく

theorem mod_refl {a:MyNat} : a ≡ a := by rfl
theorem mod_sym {a b:MyNat} : a ≡ b -> b ≡ a := by
unfold modeq
intros z
aesop
theorem mod_trans {a b c:MyNat} : a≡ b -> b ≡ c -> a ≡ c := by
unfold modeq
aesop

-- addとmulがwell-definedであることを示しておく
theorem modeq_add2 {a a' b b':MyNat} : a ≡ a' -> b ≡ b' -> a+b ≡ a'+b':= by
cases m with
|succ m' =>
generalize eq:m'.succ = m
intros c d
unfold modeq at *
rcases mod_eq a m with ⟨w1,h1⟩
rcases mod_eq b m with ⟨w2,h2⟩
rewrite [<-h1]
rewrite [<-h2]
have z:w1 * m + a % m + (w2 * m + b % m) = (a%m+b%m)+m*(w1+w2) := by ring
rewrite [z]
rewrite [mod_add]
rewrite [c,d]
rcases mod_eq a' m with ⟨w1,h1⟩
rcases mod_eq b' m with ⟨w2,h2⟩
conv =>
  rhs
  rewrite [<-h1]
  rewrite [<-h2]
have z:w1 * m + a' % m + (w2 * m + b' % m) = (a'%m+b'%m)+m*(w1+w2) := by ring
rewrite [z]
rewrite [mod_add]
rfl
apply lt_le_succ.2
exists m'
apply lt_le_succ.2
exists m'
|zero =>
intros c d
unfold modeq at *
rewrite [zero0] at *
rewrite [zero_mod] at *
rewrite [zero_mod] at *
rewrite [c,d]
rfl

theorem modeq_mul2 {a a' b b':MyNat} : a ≡ a' -> b ≡ b' -> a*b ≡ a'*b':= by
cases m with
|zero =>
intros c d
unfold modeq at *
rewrite [zero0] at *
rewrite [zero_mod] at *
rewrite [zero_mod] at *
rewrite [c,d]
rfl
|succ m' =>
  generalize eq:m'.succ = m
  intros c d
  unfold modeq at *
  rcases mod_eq a m with ⟨w1,h1⟩
  rcases mod_eq b m with ⟨w2,h2⟩
  rewrite [<-h1]
  rewrite [<-h2]
  have z:(w1 * m + a % m) * (w2 * m + b % m) = (a%m*b%m)+m*(w1*w2*m+w1*(b%m)+w2*(a%m)) := by ring
  rewrite [z]
  rewrite [mod_add]
  rcases mod_eq a' m with ⟨w1,h1⟩
  rcases mod_eq b' m with ⟨w2,h2⟩
  rewrite [<-h1]
  rewrite [<-h2]
  have z:(w1 * m + a' % m) * (w2 * m + b' % m) = (a'%m*b'%m)+m*(w1*w2*m+w1*(b'%m)+w2*(a'%m)) := by ring
  rewrite [z]
  rewrite [mod_add]
  rewrite [c,d]
  rfl
  apply lt_le_succ.2
  exists m'
  apply lt_le_succ.2
  exists m'


-- 加法の逆元の存在を示す
theorem mod_minus a : 0<m -> exists a', a+a'≡ 0 := by
intros b
have z := mod_lt a m b
apply lt_le_succ.1 at z
rcases z with ⟨w,h⟩
exists w+1
unfold modeq
simp at h
rewrite [<-add_assoc]
rcases (mod_eq a m) with ⟨ww,hh ⟩
rewrite [<-hh]
have q : ww * m + a % m + w + 1 = w+(a%m+1)+m*ww := by ring
rewrite [q,mod_add,h]
have qq : m=0+m*1 :=by ring
conv =>
  arg 1
  arg 1
  rewrite [qq]
rewrite [mod_add]
rfl
apply b
apply b

-- 素数pの場合の性質を示す

-- 積の逆元

theorem mod_rec a : is_prime m -> ¬ a≡ 0 -> exists a', a*a' ≡ 1 := by
intros b c
have eq : m.gcd a = 1 := by
  have aa := (@gcd_divides_a_and_b m a).1
  rcases b with ⟨b1,b2 ⟩
  have b3 := b2 _ aa
  cases b3 with
  |inl h=> aesop
  |inr h =>
    exfalso
    apply c
    have aaa := (@gcd_divides_a_and_b m a).2
    rewrite [h] at aaa
    rcases aaa with ⟨ww,hh ⟩
    rewrite [<-hh]
    unfold modeq
    have qqq : m*ww=0+m*ww := by ring
    rewrite [qqq,mod_add]
    rfl
    apply lt_le_succ.2
    apply lt_le_succ.1 at b1
    simp at *
    rcases b1 with ⟨cc,ccc ⟩
    exists cc+1
    ring_nf at *
    aesop
have gl := gcd_linear a m
rcases gl with ⟨p,q,r,s,eqn⟩
rewrite [eq] at eqn
have mm := mod_minus m s ?_
rcases mm with ⟨ss,h ⟩
exists q+ss
have q1 : p*m+q*a+a*ss = r*m+s*a+1+a*ss := by aesop
have q2 : r * m + s * a + 1 + a * ss ≡ 1 := by
  unfold modeq at h
  rcases mod_eq (s+ss) m with ⟨me1,me2 ⟩
  rewrite [h,<-zero0] at me2
  simp at me2
  have qq : r * m + s * a + 1 + a * ss = 1+(s+ss)*a+m*r := by ring
  rewrite [qq,<-me2]
  unfold modeq
  rewrite [mod_add]
  have qq : me1*m*a=m*(me1*a) := by ring
  rewrite [qq,mod_add]
  rfl
  apply lt_le_succ.2
  rcases b with ⟨⟨⟨b111,b112⟩ ,b12⟩ ,b2⟩
  exists b111
  apply lt_le_succ.2
  rcases b with ⟨⟨⟨b111,b112⟩ ,b12⟩ ,b2⟩
  exists b111
rewrite [<-eqn] at q2
have q3 : p*m+q*a+a*ss ≡ a*(q+ss) := by
  unfold modeq
  have z : p*m+q*a+a*ss = a*(q+ss)+m*p := by ring
  rewrite [z,mod_add]
  rfl
  apply lt_le_succ.2
  rcases b with ⟨⟨b11,b12⟩ ,_⟩
  apply b11
apply mod_trans
apply mod_sym
apply q3
apply q2
apply lt_le_succ.2
rcases b with ⟨⟨b11,b12⟩ ,_⟩
apply b11

end modulo

section modulo1


open binom


variable (p:MyNat)
local infix:50 " ≡ " => modulo.modeq p
-- a^p

theorem pow_p_id : is_prime p -> forall a:MyNat, pow a p ≡ a := by
intros b a
rcases b with ⟨b1,b2⟩
apply lt_le_succ.1 at b1
rcases b1 with ⟨c1,c2 ⟩
rewrite [<-zerosucc,add_succ,add_succ,zero0,add_zero] at c2
induction a with
| zero =>
  have z : pow zero p = zero := by
    rewrite [<-c2]
    unfold pow
    unfold repeatn
    simp
  rewrite [z]
  apply modulo.mod_refl
|succ a' ih =>
  rewrite [succ_add_one]
  rewrite [pow4]
  rewrite [<-c2]
  unfold accumulate
  rewrite [accum2]
  rewrite [c2]
  rewrite [(binom1 p).1]
  rewrite [one_mul]
  apply modulo.modeq_add2
  apply ih
  conv =>
    lhs
    arg 1
    arg 1
    unfold binom
    rewrite [<-c2]
    simp
    rewrite [<-zero0]
    simp
  conv =>
    lhs
    arg 1
    arg 2
    simp
    rewrite [<-zerosucc]
    unfold repeatn
    simp
    rewrite [<-zero0]
    simp
  rewrite [mul_one]
  conv =>
    rhs
    rewrite [<-MyNat.zero_add 1]
  apply modulo.modeq_add2
  apply modulo.mod_refl
  have z : forall cx, cx.succ < p -> p ∣ (accumulate (fun z => binom p (z + 1) * pow a' (z + 1)) cx) := by
    intros cx hx
    induction cx with
    |zero =>
      unfold accumulate
      have bp := binom_prime p ?_ 1 ?_ ?_
      ring_nf
      rcases bp with ⟨w,h⟩
      exists w*pow a' 1
      rewrite [<-mul_assoc]
      rewrite [h]
      rfl
      unfold is_prime
      constructor
      apply lt_le_succ.2
      exists c1
      apply b2
      apply lt_le_succ.2
      exists 0
      apply lt_le_succ.2
      exists c1
    |succ cx' ih =>
      unfold accumulate
      have q : cx'.succ<p := by
        apply MyNat.lt_trans
        apply lt_le_succ.2
        exists 0
        rewrite [zero_add]
        apply hx
      have ihh := ih q
      rcases ihh with ⟨w,h⟩
      rewrite [<-h]
      have b1 := binom_prime p ?_ (cx'.succ+1) ?_ ?_
      rcases b1 with ⟨ww,hh⟩
      rewrite [<-hh]
      exists ww * pow a' (cx'.succ + 1) + w
      ring
      unfold is_prime
      constructor
      apply lt_le_succ.2
      exists c1
      simp
      intros k x q
      apply b2
      exists x
      apply lt_le_succ.2
      exists cx'+1
      rewrite [succ_add_one] at hx
      apply hx
  have zz := z c1 ?_
  rcases  zz with ⟨w,h⟩
  rewrite [<-h]
  unfold modulo.modeq
  have zzz : p*w = 0+p*w := by ring
  rewrite [zzz]
  apply mod_add
  apply lt_le_succ.2
  exists c1.succ
  apply lt_le_succ.2
  exists 0
  rewrite [succ_add_one] at c2
  rewrite [succ_add_one] at c2
  simp
  ring_nf
  ring_nf at c2
  apply c2

end modulo1
