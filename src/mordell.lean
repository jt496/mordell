import
  tactic
  data.complex.basic
  algebra.euclidean_domain.basic
  .rt_7_ring

namespace ℤα
variables (a b : ℤα)
#check a+b
#eval (⟨1,2⟩: ℤα)
#print instances  euclidean_domain

open complex
open euclidean_domain

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

--Shows that the factorization of y^2-y+2 is valid.
lemma my_factorization (y:ℤ):
  (y:ℤα)^2-y+2 = (y-α)*(y-α_bar):=
  begin
  transitivity (y:ℤα)^2 - (α+α_bar)*y + α*α_bar, {
    congr,
    have r : α + α_bar = one := by ring_nf,
    rw r,
    have h := my_one_mul,
    specialize h (y:ℤα),
    have q : one*(y:ℤα)=(y:ℤα) := h,
    rw q,
  },
  ring_nf,
  end

lemma factors_coprime : ∀y:ℤ, is_coprime ((y:ℤα)-α) ((y:ℤα)-α_bar) :=
begin
  intro y,
  by_contra,
  sorry,
end

lemma norm_divides (a p : ℤα):
  (p ∣ a) → ((nat_Norm p) ∣ (nat_Norm a)):=
  begin
  intro h,
  have r : (∃ k : ℕ, (nat_Norm p)*k = nat_Norm a) → ((nat_Norm p) ∣ (nat_Norm a)):=
  begin
    sorry
  end,
  have s : (p ∣ a) → ∃ k : ℤα, p*k = a:= by sorry,
  have q := s h,
  apply r,
  clear h r s,
  cases q with n hn,
  use nat_Norm n,
  rw ← nat_Norm_mul p n,
  rw hn,
  end




--Main theorem
theorem dioph_eq (x y: ℤ) : 
  x^3=y^2-y+2 → (x=2 ∧ y=-2) ∨ (x=2 ∧ y=3) :=
  begin
  intro h,
  sorry,
  end

end ℤα
