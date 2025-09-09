import mynat

open MyNat

variable (m : MyNat)

def modeq (a b:MyNat) := mod a m = mod b m

local infix:50 " ≡ " => modeq m

theorem mod_refl {a:MyNat} : a ≡ a := by rfl
theorem mod_sym {a b:MyNat} : a ≡ b -> b ≡ a := by
unfold modeq
intros z
aesop
theorem mod_trans {a b c:MyNat} : a≡ b -> b ≡ c -> a ≡ c := by
unfold modeq
aesop
