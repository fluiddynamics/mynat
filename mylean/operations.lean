import mynat

open MyNat

inductive MyAdd :MyNat -> MyNat -> MyNat -> Prop where
  | init : MyAdd zero zero zero
  | left{a b c} : MyAdd a b c -> MyAdd a.succ b c.succ
  | right{a b c} : MyAdd a b c -> MyAdd a b.succ c.succ

theorem lemma1 : forall a b c, MyAdd a.succ b c -> MyAdd a b.succ c := by
intros a b c
intros d
generalize h:a.succ = aa
rewrite [h] at d
induction d with
|init =>
  injection h
|left z x =>
  injection h with aeq
  rewrite [aeq]
  apply MyAdd.right
  apply z
|right z x =>
  apply MyAdd.right
  apply x
  apply h

theorem myadd_equiv : forall a b c, a+b=c ↔ MyAdd a b c := by
intros a
induction a with
|zero =>
  intros b
  induction b with
  | zero =>
    intros c
    constructor
    intros d
    simp at d
    simp
    rewrite [<-d]
    apply MyAdd.init
    intros d
    cases d
    simp
  | succ b' b_ih =>
    intros c
    constructor
    intros d
    simp
    simp at d
    rewrite [<-d]
    rewrite [<-succ_add_one]
    apply MyAdd.right
    apply (b_ih b').1
    simp
    intros d
    cases d
    case right x y
    have z := (b_ih x).2 y
    simp
    simp at z
    rewrite [z]
    simp
|succ a' a_ih=>
  intros b c
  constructor
  intros d
  rewrite [add_succ] at d
  cases c with
  | zero =>
    injection d
  |succ c' =>
    injection d
    case succ.mp.succ eq
    have aa := (a_ih b c').1 eq
    apply MyAdd.left
    apply aa
  intros d
  have l1 := lemma1 _ _ _ d
  have l2 := (a_ih _ _).2 l1
  rewrite [add_succ]
  rewrite [<-succ_add]
  apply l2

inductive MyAdd2 :MyNat -> MyNat -> MyNat -> Prop where
  | left{a} : MyAdd2 0 a a
  | right{a b c} : MyAdd2 a b.succ c -> MyAdd2 a.succ b c

theorem myadd2_equiv : forall a b c, a+b=c ↔ MyAdd2 a b c := by
intros a
induction a with
|zero =>
  intros b c
  constructor
  intros d
  simp at d
  rewrite [d]
  apply MyAdd2.left
  intros d
  cases d with
  | left =>
    simp
| succ a' ih=>
  intros b
  induction b with -- この帰納法はおそらく不要
  |zero =>
    intros c
    constructor
    intros d
    rewrite [add_succ,<-succ_add] at d
    have ih1 := (ih _ _).1 d
    apply MyAdd2.right ih1
    intros d
    cases d with
    |right dd=>
      have z :=(ih _ _).2 dd
      rewrite [succ_add,<-add_succ] at z
      apply z
  |succ b' ih2 =>
    intros c
    constructor
    intros d
    have z: MyAdd2 a' b'.succ.succ c := by
      rewrite [add_succ,<-succ_add] at d
      apply (ih _ _).1 d
    apply MyAdd2.right z
    intros d
    cases d with
    |right z =>
      have x := (ih _ _).2 z
      simp at x
      ring_nf at x
      simp
      ring_nf
      apply x
