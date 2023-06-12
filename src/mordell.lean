import
  tactic
  data.complex.basic
  ring_theory.euclidean_domain
  .rt_7_ring
  ring_theory.coprime.basic
  ring_theory.principal_ideal_domain
  number_theory.divisors

namespace ℤα
variables (a b : ℤα)
#check a+b
#eval (⟨1,2⟩: ℤα)
#print instances  euclidean_domain

open complex
open int
open euclidean_domain

section mordell
parameters { x y : ℤ } {sol : x^3 = y^2 - y + 2}

instance : is_principal_ideal_ring ℤα := infer_instance
#print instances is_principal_ideal_ring

#print instances normalized_gcd_monoid

noncomputable
def d := gcd ((y:ℤα)-α) ((y:ℤα)-α_bar)

lemma conj_α: star_ring_end ℂ complex_α = α_bar :=
  begin
  unfold α_bar complex_α,
  have h : star_ring_end ℂ ⟨1/2, (rt_7/2)⟩ = ⟨1/2, -rt_7/2⟩ := by ring_nf,
  rw h,
  clear h,
  have p := re_of_coe,
  have q := im_of_coe,
  specialize p (⟨1, -1⟩:ℤα),
  specialize q (⟨1, -1⟩:ℤα),
  simp at p q,
  ring_nf at p,
  ext,
  rw p,
  rw q,
  end 

  lemma norm_divides (a p : ℤα):
  (p ∣ a) → (Norm p ∣ Norm a):=
  begin
  intro h,
  have r : (∃ k : ℤ, Norm a = (Norm p)*k) → ((Norm p) ∣ (Norm a)):=
    begin
    rintro ⟨k, hk⟩,
    use k,
    exact hk,
    end,
  have s : (p ∣ a) → ∃ k : ℤα, a = p*k:=
    begin
    rintro ⟨r, hr⟩,
    use r,
    exact hr,
    end,
  have q := s h,
  apply r,
  clear h r s,
  cases q with n hn,
  use Norm n,
  rw ← Norm_mul p n,
  rw hn,
  end

lemma coe_from_ints (a:ℤ) : (a:ℤα) = (⟨a, 0⟩:ℤα) :=
begin
sorry,
end

--Shows that the factorization of y^2-y+2 is valid.
lemma my_factorization:
  (y:ℤα)^2-y+2 = (y-α)*(y-α_bar):=
  begin
  transitivity (y:ℤα)^2 - (α+α_bar)*y + α*α_bar, {
    congr,
    have r : α + α_bar = one := by ring_nf,
    rw r,
    have q : one*(y:ℤα)=(y:ℤα) := my_one_mul (y:ℤα),
    rw q,
  },
  ring_nf,
  end

lemma d_dvd_sqrt_seven_i : d ∣ α - α_bar :=
begin
change ∃(k:ℤα), α - α_bar = d*k,
have h : d ∣ y - α := gcd_dvd_left (y - α) (y - α_bar),
have q : d ∣ y - α_bar := gcd_dvd_right (y - α) (y - α_bar), 
change ∃(j:ℤα), (y:ℤα) - α = d*j at h,
change ∃(g:ℤα), (y:ℤα) - α_bar = d*g at q,
cases h with j hj,
cases q with g hg,
use (g - j),
rw mul_sub,
rw ←  hg,
rw ← hj,
ring_nf,
end

lemma norm_seven : Norm (α - α_bar) = 7 :=
begin
unfold Norm α α_bar,
ring_nf,
end

--Why is it showing y:ℤ as a hypothesis?
lemma nd_dvd_seven : Norm d ∣ 7 :=
begin
have h := d_dvd_sqrt_seven_i,
have q := norm_divides (α - α_bar) d h,
rw norm_seven at q,
exact q,
end

lemma nd_one_or_seven : Norm d = 1 ∨ Norm d = 7 :=
begin
sorry,
end

lemma norm_y_minus_α : Norm (y-α) = y^2 - y + 2 :=
begin
have h : (y:ℤα)-α = (⟨y,-1⟩:ℤα) := by sorry,
rw h,
unfold Norm,
ring_nf,
end

-- Using the fact that d divides y-α
lemma nd_dvd_pol : Norm d ∣ y^2 - y + 2 :=
begin
sorry,
end

lemma sev_dvd_x_cubed (h : 7 ∣ x^3) : 7 ∣ x :=
begin
sorry,
end

#check mod_nonneg
#check int.mod_lt

-- find mathlib lemma for y % 7 = 4 → ∃k, y = 7k+4
-- use interval_cases and the above lemmas
lemma seven_dvd_pol (h : 7 ∣ y^2 - y + 2) : y % 7 = 4 :=
begin
sorry,
end

--gcd_is_unit_iff is a useful theorem

lemma unit_iff_norm_one (a : ℤα) : is_unit a ↔ Norm a = 1 :=
begin
sorry,
end

lemma units_are (a : ℤαˣ): a = 1 ∨ a = -1 := 
begin
sorry,
end

lemma irred_pol : ¬(7^2 ∣ y^2 - y + 2) := 
begin
sorry,
end

lemma factors_coprime : is_coprime ((y:ℤα)-α) ((y:ℤα)-α_bar) :=
begin
  by_contra,
  sorry,
end

--Main theorem
theorem dioph_eq (x y: ℤ) : 
  x^3=y^2-y+2 → (x=2 ∧ y=-2) ∨ (x=2 ∧ y=3) :=
  begin
  intro h,
  sorry,
  end


end mordell
end ℤα


