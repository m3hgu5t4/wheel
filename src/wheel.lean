import algebra.ring.basic
import tactic
set_option old_structure_cmd true

/-- A type endowed with `0`, `1` and `+` is an additive commutative monoid with one,
if it admits an injective map that preserves `0`, `1` and `+` to an additive commutative monoid with
one. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.add_comm_monoid_with_one {M₁ M₂} [has_zero M₁] [has_one M₁] [has_add M₁] [has_smul ℕ M₁]
  [has_nat_cast M₁] [add_comm_monoid_with_one M₂] (f : M₁ → M₂) (hf : function.injective f) (zero : f 0 = 0)
  (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) :
  add_comm_monoid_with_one M₁ :=
{ ..hf.add_monoid_with_one f zero one add nsmul nat_cast, ..hf.add_comm_monoid f zero add nsmul }

universes u

@[protect_proj, ancestor add_monoid_with_one comm_monoid]
class wheel (α : Type u) extends add_comm_monoid_with_one α, comm_monoid α :=
(div : α → α)
(div_invol : ∀ x, div (div x) = x)
(div_mul_distrib : ∀ x y, div (x * y) = div x * div y)
(add_distrib_mul : ∀ x y z, (x + y) * z + (0 : α) * z = x * z + y * z)
(add_distrib_div : ∀ x y z, (x + y * z) * div y = x * div y + z + (0 : α) * y)
(zero_mul : (0 : α) * (0 : α) = 0)
(add_zero_mul : ∀ x y z, (x + (0 : α) * y) * z = x * z + (0 : α) * y)
(div_add_zero : ∀ x y, div (x + (0 : α) * y) = div x + 0 * y)
(add_bot : ∀ x, 0 * div 0 + x = (0 : α) * div 0)

attribute [simp] wheel.div_invol wheel.div_mul_distrib wheel.add_distrib_mul wheel.zero_mul wheel.add_bot

-- localized "notation (name := wheel.bot) `⊥` := (0 * wheel.div 0 : wheel)" in wheel
-- localized "notation (name := wheel.infinity) `∞` := (wheel.div 0 : wheel)" in wheel
-- localized "prefix `/`:(std.prec.max + 4) := wheel.div" in wheel
prefix `/`:(std.prec.max + 4) := wheel.div
notation (name := wheel.infinity) `∞w` := (wheel.div 0)
notation (name := wheel.bot) `⊥w` := (0 * ∞w)

namespace wheel

variables {W : Type u} [wheel W]

lemma zero_mul_add : ∀ (x y : W), 0 * (x + y) = 0 * x + 0 * y :=
begin
  intros x y,
	rw mul_comm,
	nth_rewrite 1 mul_comm,
	nth_rewrite 2 mul_comm,
	simpa using wheel.add_distrib_mul x y 0,
end

@[simp]
lemma div_one_eq_one : /(1 : W) = 1 :=
begin
	calc /(1 : W)
	    = (1 : W) * /(1 : W) : (one_mul _).symm
	... = /(/(1 : W)) * /(1 : W) : by rw wheel.div_invol
	... = /(/(1 : W) * 1) : by rw wheel.div_mul_distrib
	... = /(/(1 : W)) : by rw mul_one
	... = 1 : wheel.div_invol _,
end

lemma zero_mul_mul_eq_zero_mul_add_zero_mul : ∀ (x y : W), 0 * x + 0 * y = 0 * x * y :=
begin
	intros x y,
	rw (wheel.add_zero_mul 0 y x).symm,
  rw [zero_add, mul_assoc], 
	nth_rewrite 1 mul_comm,
	rwa ← mul_assoc,
end

lemma bot_mul : ∀ (x : W), ⊥w * x = ⊥w :=
begin
	intro x,
	rw ← zero_mul_mul_eq_zero_mul_add_zero_mul ∞w x,
	exact wheel.add_bot (0 * x),
end

lemma div_self : ∀ (x : W), x * /x = 1 + 0 * x * /x :=
begin
	intro x,
	have := wheel.add_distrib_div 0 x 1,
	rw [zero_add, mul_one] at this,
	rw [this, add_assoc, add_comm, add_assoc],
	rwa zero_mul_mul_eq_zero_mul_add_zero_mul,
end

lemma mul_cancel : ∀ (x y z : W), x * z = y * z → x + 0 * z * /z = y + 0 * z * /z :=
begin
	intros x y z h,
	have : x * z * /z = y * z * /z := congr_arg (λ p, p * /z) h,
	rw [mul_assoc, mul_assoc] at this,
	rw div_self z at this,
	rw [mul_comm, mul_comm y _, mul_assoc] at this,
	rw [wheel.add_zero_mul 1 _ x, wheel.add_zero_mul 1 _ y, one_mul, one_mul] at this,
	rwa mul_assoc,
end

lemma zero_eq_one_imp_one_eq_bot : 0 = (1 : W) → (1 : W) = ⊥w :=
begin
	intro h,
	calc 1
	    = 1 * 1 : (mul_one 1).symm
	... = 1 * /(1 : W) : by rw div_one_eq_one
	... = 0 * /0 : by rw h,
end

lemma zero_eq_infty_imp_zero_eq_bot : (0 : W) = ∞w → (0 : W) = ⊥w :=
begin
	intro h,
	calc 0 
		  = 0 * 0 : wheel.zero_mul.symm
	... = 0 * /(0 : W) : by rw ← h,
end

lemma zero_eq_bot_imp_eq_bot : (0 : W) = ⊥w → ∀ (x : W), x = ⊥w :=
begin
	intros h x,
	calc x
			= 0 + x : (zero_add x).symm
	... = 0 * /0 + x : by rw ← h
	... = 0 * /0 : wheel.add_bot _,
end

lemma one_eq_infty_imp_one_eq_bot : (1 : W) = ∞w → (1 : W) = ⊥w :=
begin
	intro h,
	calc (1 : W)
	    = 1 * /1 : by rw [one_mul, div_one_eq_one]
	... = /0 * /(/0) : by rw h
	... = 0 * /0 : by rw [wheel.div_invol, mul_comm],
end

lemma one_eq_bot_imp_eq_bot : (1 : W) = ⊥w → ∀ (x : W), x = ⊥w :=
begin
	intros h x,
	calc x
			= 1 * x : (one_mul x).symm
	... = 0 * /0 * x : by rw h
	... = 0 * /0 : bot_mul x,
end

lemma bot_eq_infinity_imp_eq_bot : (∞w : W) = ⊥w → ∀ (x : W), x = ⊥w :=
begin
	intros h x,
	calc x
			= 0 + x : (zero_add x).symm
	... = /(/0) + x : by rw wheel.div_invol
	... = /(0 * /0) + x : by rw ← h
	... = 0 * /(0) + x : by rw [wheel.div_mul_distrib, wheel.div_invol, mul_comm]
	... = 0 * /0 : wheel.add_bot _,
end

lemma zero_one_bot_infinity_unique : ((0 : W) = 1) ∨ ((0 : W) = ∞w) ∨ ((0 : W) = ⊥w) ∨ ((1 : W) = ∞w) ∨ ((1 : W) = ⊥w) ∨ ((∞w : W) = ⊥w) → ∀ (x y : W), x = y :=
begin
	intro h,
	suffices : ∀ x, x = (0 : W) * /0,
	{ intros x y, exact (this x).trans (this y).symm, },
	obtain (h | h | h | h | h | h) := h,
	{ exact one_eq_bot_imp_eq_bot (zero_eq_one_imp_one_eq_bot h), },
	{ exact zero_eq_bot_imp_eq_bot (zero_eq_infty_imp_zero_eq_bot h), },
	{ exact zero_eq_bot_imp_eq_bot h, },
	{ exact one_eq_bot_imp_eq_bot (one_eq_infty_imp_one_eq_bot h), },
	{ exact one_eq_bot_imp_eq_bot h, },
	{ exact bot_eq_infinity_imp_eq_bot h, }
end


-- class unit (α : Type u) [wheel α] (x : α) :=
-- (inverse : α)
-- (mul_inverse : x * inverse = 1)

lemma inverse_div_rel (x : W) [invertible x] : ⅟ x + 0 * /x = /x + 0 * ⅟ x :=
begin
	calc ⅟ x + 0 * /x
	    = ⅟ x * /(x * ⅟ x) + 0 * /x : by rw [mul_inv_of_self, div_one_eq_one, mul_one]
	... = /x * (⅟ x * /(⅟ x)) + 0 * /x : by { rw [wheel.div_mul_distrib], nth_rewrite 1 mul_comm, rw [← mul_assoc, mul_comm], }
	... = /x + 0 * ⅟ x * /(x * ⅟ x) : by { rw [div_self, mul_comm, wheel.add_distrib_mul, one_mul, wheel.div_mul_distrib], nth_rewrite 5 mul_comm, rw ← mul_assoc, }
	... = /x + 0 * ⅟ x : by rw [mul_inv_of_self, div_one_eq_one, mul_one],
end

lemma inverse_eq_div_add_zero_mul_inverse_self_div (x : W) [invertible x] : ⅟ x = /x + 0 * ⅟ x * /(⅟ x) :=
begin
	rw [← zero_mul_mul_eq_zero_mul_add_zero_mul, ← add_assoc, ← inverse_div_rel, add_assoc, zero_mul_mul_eq_zero_mul_add_zero_mul, mul_assoc, ← wheel.div_mul_distrib, mul_inv_of_self, div_one_eq_one, mul_one, add_zero],
end

lemma div_eq_mul_add_self_div (x : W) [invertible x] : /x = ⅟ x + 0 * x * /x :=
begin
	rw ← zero_mul_mul_eq_zero_mul_add_zero_mul,
	nth_rewrite 1 add_comm,
	rw [← add_assoc, inverse_div_rel, add_assoc, zero_mul_mul_eq_zero_mul_add_zero_mul, mul_assoc],
	nth_rewrite 1 mul_comm,
	rw [mul_inv_of_self, mul_one, add_zero],
end

def zero_mul_self_and_div_self_imp_unit : ∀ x : W, (0 * x = 0 ∧ 0 * /x = 0) → invertible x :=
λ x hx, ⟨/x, by rw [mul_comm, wheel.div_self, hx.1, hx.2, add_zero], by rw [wheel.div_self, hx.1, hx.2, add_zero]⟩


@[reducible]
def 𝓡 (α : Type u) [wheel α] := {x : α // (0 : α) * x = 0}

namespace 𝓡

instance : has_zero (𝓡 W) :=
{ zero := ⟨0, wheel.zero_mul⟩ }

instance : has_one (𝓡 W) :=
{ one := ⟨1, mul_one 0⟩ }

instance : has_add (𝓡 W) :=
{ add := λ x y, ⟨x.1 + y.1, 
		begin
			calc 0 * (x.1 + y.1)
					= (x.1 + y.1) * 0 + 0 * 0 : by rw [wheel.zero_mul, add_zero, mul_comm]
			... = x.1 * 0 + y.1 * 0 : wheel.add_distrib_mul _ _ _
			... = 0 : by rw [mul_comm, x.2, mul_comm, y.2, add_zero],
		end⟩, }

instance : has_smul ℕ (𝓡 W) :=
{ smul := λ n x, ⟨n • x.1, by { 
	induction n, 
	{ rw [zero_nsmul, wheel.zero_mul] },
	{ rw [succ_nsmul],
		set nx : 𝓡 W := ⟨n_n • x.val, n_ih⟩,
		exact (x + nx).prop, } }⟩ }

instance : has_nat_cast (𝓡 W) :=
{ nat_cast := λ N, ⟨N, by { 
	induction N,
	{ rw [nat.cast_zero, wheel.zero_mul] },
	{ rw nat.cast_succ,
		exact (⟨N_n, N_ih⟩ + 1 : 𝓡 W).prop, } }⟩ }

instance : add_comm_monoid_with_one (𝓡 W) :=
subtype.coe_injective.add_comm_monoid_with_one _ rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)

instance : has_mul (𝓡 W) :=
{ mul := λ x y, ⟨x.1 * y.1,
		begin
			rw [← mul_assoc, ← wheel.zero_mul_mul_eq_zero_mul_add_zero_mul],
			dsimp, rw [x.prop, y.prop, add_zero],
		end⟩, }

instance : has_pow (𝓡 W) ℕ :=
{ pow := λ x n, ⟨x.1 ^ n, 
		begin
			induction n,
			{ rw [pow_zero, mul_one], },
			{ rw [pow_succ, ← mul_assoc, ← wheel.zero_mul_mul_eq_zero_mul_add_zero_mul, n_ih],
				dsimp, rw [x.prop, add_zero], }
		end⟩ }

instance : comm_monoid (𝓡 W) :=
subtype.coe_injective.comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

@[simp, norm_cast] lemma coe_zero : ((0 : 𝓡 W) : W) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : 𝓡 W) : W) = 1 := rfl
@[simp, norm_cast] lemma coe_add (a b : 𝓡 W) : (↑(a + b) : W) = a + b := rfl
@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (a : 𝓡 W) : (↑(n • a) : W) = n • a := rfl
@[simp, norm_cast] lemma coe_nat_cast (n : ℕ) : ((n : 𝓡 W) : W) = n := rfl
@[simp, norm_cast] lemma coe_mul (a b : 𝓡 W) : (↑(a * b) : W) = a * b := rfl
-- @[simp, norm_cast] lemma coe_pow (a : 𝓡 W) ℕ : (↑(a ^ n) : W) = a ^ n := rfl

instance : comm_semiring (𝓡 W) :=
{ left_distrib := 
		begin
			intros a b c,
			ext, rw [coe_mul, coe_add, coe_add, coe_mul, coe_mul],
			nth_rewrite 1 mul_comm, nth_rewrite 2 mul_comm,
			rw [← wheel.add_distrib_mul, a.prop, add_zero, mul_comm],
		end,
  right_distrib :=
		begin
			intros a b c,
			ext, rw [coe_mul, coe_add, coe_add, coe_mul, coe_mul],
			rw [← wheel.add_distrib_mul, c.prop, add_zero],
		end,
  zero_mul := 
		begin
			intro a, 
			ext, rw [coe_zero, coe_mul, coe_zero, a.prop],
		end,
  mul_zero := 
		begin
			intro a,
			ext,
			rw [mul_comm, coe_zero, coe_mul, coe_zero, a.prop],
		end,
  ..𝓡.add_comm_monoid_with_one, ..𝓡.comm_monoid }

end 𝓡

@[reducible]
def 𝓢 (α : Type u) [wheel α] := {x : α // 0 * x = 0 ∧ 0 * /x = 0}

namespace 𝓢

instance : has_one (𝓢 W) :=
{ one := ⟨1, mul_one 0, by rw [div_one_eq_one, mul_one] ⟩ }

instance : has_mul (𝓢 W) :=
{ mul := λ x y, ⟨x.1 * y.1, 
		begin
			dsimp, split,
			{ rw [← mul_assoc, ← wheel.zero_mul_mul_eq_zero_mul_add_zero_mul, x.prop.1, y.prop.1, add_zero], },
			{ rw [wheel.div_mul_distrib, ← mul_assoc, x.prop.2, y.prop.2] }
		end⟩ }

instance : has_pow (𝓢 W) ℕ :=
{ pow := λ x n, ⟨x.1 ^ n,
		begin
			induction n,
			{ simp only [pow_zero, mul_one, div_one_eq_one, and_self], },
			{ rw pow_succ, dsimp at n_ih ⊢, rw [← mul_assoc, wheel.div_mul_distrib, ← mul_assoc, x.prop.1, x.prop.2, n_ih.1, n_ih.2], exact ⟨rfl, rfl⟩, }
		end⟩ }

instance : comm_monoid (𝓢 W) :=
subtype.coe_injective.comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

instance : has_inv (𝓢 W) :=
{ inv := λ x, ⟨/x.val, x.prop.2, by { rw wheel.div_invol, exact x.prop.1, }⟩ }

@[simp, norm_cast] lemma coe_one : ((1 : 𝓢 W) : W) = 1 := rfl
@[simp, norm_cast] lemma coe_mul (a b : 𝓢 W) : (↑(a * b) : W) = a * b := rfl
@[simp, norm_cast] lemma coe_inv (a : 𝓢 W) : (↑(a⁻¹) : W) = /a := rfl

instance : comm_group (𝓢 W) :=
{ mul_left_inv :=
		begin
			intro a,
			ext, simp only [coe_mul, coe_inv, coe_one],
			rw [mul_comm, wheel.div_self, a.prop.1, a.prop.2, add_zero],
		end,
	..𝓢.comm_monoid, ..𝓢.has_inv }

end 𝓢

end wheel

-- wheel with an element that behaves as -1
class sub_wheel (α : Type u) extends wheel α :=
(minus_one : α)
(minus_one_plus_one : 1 + minus_one = 0)

attribute [simp] sub_wheel.minus_one_plus_one

prefix (name := sub_wheel.neg) `-`:(std.prec.max + 5) := sub_wheel.mul sub_wheel.minus_one

namespace sub_wheel

variables {W : Type u} [sub_wheel W]

lemma add_neg_self : ∀ x : W, x + -x = 0 * x * x :=
begin
	intro x,
	calc x + minus_one * x
	    = 1 * x + minus_one * x : by rw one_mul
	... = (1 + minus_one) * x + 0 * x : by rw ← add_distrib_mul
	... = 0 * x + 0 * x : by rw minus_one_plus_one
	... = 0 * x * x : by rw wheel.zero_mul_mul_eq_zero_mul_add_zero_mul,
end

end sub_wheel
