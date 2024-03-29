import
  tactic
  data.complex.basic
  ring_theory.euclidean_domain
  .rt_2_ring
  .cubic_ring
  ring_theory.coprime.basic
  ring_theory.principal_ideal_domain
  number_theory.divisors
  algebra.group.units
  data.nat.prime
  ring_theory.int.basic
  algebra.ring.divisibility
  data.nat.prime_norm_num
  algebra.gcd_monoid.basic
  algebra.group.units
  algebra.group.defs
  algebra.associated


open_locale classical

--set_option profiler true


namespace ℤα
--variables (a b : ℤα)
-- #check a+b
-- #eval (⟨1,2⟩: ℤα)
-- #print instances  euclidean_domain

section mordell
parameters { x y : ℤ } (sol: x^3 = y^2 - 2)

noncomputable
instance : gcd_monoid  ℤα:=
{ gcd := λ a b, euclidean_domain.gcd a b,
  lcm := λ a b, euclidean_domain.lcm a b,
  gcd_dvd_left := λ a b, euclidean_domain.gcd_dvd_left a b,
  gcd_dvd_right := λ a b, euclidean_domain.gcd_dvd_right a b,
  dvd_gcd := λ  a b c hac hab, euclidean_domain.dvd_gcd hac hab,
  gcd_mul_lcm := begin
    intros a b,
    have h := euclidean_domain.gcd_mul_lcm a b,
    use 1,
    simp,
  end,
  lcm_zero_left := λ a, euclidean_domain.lcm_zero_left a,
  lcm_zero_right := λ a, euclidean_domain.lcm_zero_right a }

instance : is_principal_ideal_ring ℤα := infer_instance
-- #print instances is_principal_ideal_ring
-- #print instances gcd_monoid
-- #print instances is_domain

noncomputable
def d := euclidean_domain.gcd ((y:ℤα) + α) ((y:ℤα)- α)

/- 
We work towards showing that (y+α) and (y-α) are coprime, i.e.
their gcd (represented by d) is a unit. By considering the difference of the 
two terms, we find Norm d | 8. Also, x has to be odd. We have that d | x^3
which implies Norm d | x^6 (odd). This gives Norm d = 1.
-/

lemma Norm_divides {p a : ℤα} (h : p ∣ a) : (Norm p ∣ Norm a):=
  begin
  cases h with n hn,
  use Norm n,
  rw ← Norm_mul p n,
  rw hn,
  end

--Shows that the factorization of y^2-2 is valid.
lemma my_factorization: (y:ℤα)^2-2 = (y+α)*(y-α):=
begin
transitivity (y:ℤα)^2 - α^2,
congr,
rw sq_sub_sq _ _,
end

/- d = gcd (y+α) (y-α) divides the difference of
   (y+α) and (y-α), which is 2*sqrt(2). -/

lemma d_dvd_2_sqrt_2 : d ∣ 2*α :=
begin
change d ∣ α + α,
change ∃(k:ℤα), α + α = d*k,
have h : d ∣ y + α := euclidean_domain.gcd_dvd_left (y + α) (y - α),
have q : d ∣ y - α := euclidean_domain.gcd_dvd_right (y + α) (y - α),
cases h with j hj,
cases q with g hg,
use (j - g),
rw mul_sub,
rw ← hj,
rw ← hg,
rw ← sub_add,
nth_rewrite 2 add_comm,
rw add_sub_cancel (α:ℤα) (y:ℤα),
end

lemma Norm_d_dvd_eight : Norm d ∣ 8 :=
begin
have h := Norm_divides d_dvd_2_sqrt_2,
have p : Norm (2*α) = 8 := by ring_nf,
rw p at h,
exact h,
end

lemma mod_equiv {n:ℤ} {k:ℤ} {s:ℤ} (h : n % k = s) : ∃(m:ℤ), n = k*m + s :=
begin
obtain ⟨l, lh⟩ := int.dvd_sub_of_mod_eq h,
use l,
exact eq_add_of_sub_eq lh,
end 

---------------------------------------------
-- Let the pain begin

lemma y_eq_zero_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 0) : false :=
begin
have t := mod_equiv p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ 64*k^2,{
use 8*k^2,
ring_nf,
},
rw sub_eq_add_neg at h,
rw dvd_add_right r at h,
rw ← dvd_abs at h,
norm_num at h,
end

lemma y_eq_one_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 1) : false :=
begin
have t := mod_equiv p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+16)*k, {
use (8*k+2)*k,
ring_nf,
},
rw sub_eq_add_neg at h,
rw dvd_add_right r at h,
rw ← dvd_abs at h,
norm_num at h,
end

lemma y_eq_two_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 2) : false :=
begin
have t := mod_equiv p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+32)*k, {
use (8*k+4)*k,
ring_nf,
},
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_three_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 3) : false :=
begin
have t := mod_equiv p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+48)*k, {
use (8*k+6)*k,
ring_nf,
},
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_four_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 4) : false :=
begin
have t := mod_equiv p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+64)*k, {
use (8*k+8)*k,
ring_nf,
},
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_five_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 5) : false :=
begin
have t := mod_equiv p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+80)*k+16, {
use (8*k+10)*k+2,
ring_nf,
},
have bob : (23:ℤ) = 16 + 7 := by dec_trivial,
rw bob at h,
rw ← add_assoc at h,
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_six_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 6) : false :=
begin
have t := mod_equiv p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+96)*k+32, {
use (8*k+12)*k+4,
ring_nf,
},
have bob : (34:ℤ) = 32 + 2 := by dec_trivial,
rw bob at h,
rw ← add_assoc at h,
rw dvd_add_right r at h,
norm_num at h,
end

lemma y_eq_seven_mod_eight (h : 8 ∣ y^2 - 2) (p : y % 8 = 7) : false :=
begin
have t := mod_equiv p,
cases t with k hk,
rw hk at h,
ring_nf at h,
have r : 8 ∣ (64*k+112)*k+40, {
use (8*k+14)*k+5,
ring_nf,
},
have bob : (47:ℤ) = 40 + 7 := by dec_trivial,
rw bob at h,
rw ← add_assoc at h,
rw dvd_add_right r at h,
norm_num at h,
end

-----------------------------------------------

include sol
lemma x_odd : ¬ 2 ∣ x :=
begin
-- by_contra,
-- have k := pow_dvd_pow_of_dvd h 3,
-- have l : (2:ℤ)^3 = 8 := by norm_num,
-- rw l at k,
-- rw sol at k,

-- have : (8:ℤ) ≠ 0 := by dec_trivial,
-- have flop : 0 ≤ (8:ℤ)  := by dec_trivial,
-- have dip := int.mod_lt y this,
-- have jop := int.mod_nonneg y this,
-- rw ← abs_eq_self at flop,
-- rw flop at dip,
-- clear this flop l h sol,
-- interval_cases using jop dip,
-- exact y_eq_zero_mod_eight k h,
-- exact y_eq_one_mod_eight k h,
-- exact y_eq_two_mod_eight k h,
-- exact y_eq_three_mod_eight k h,
-- exact y_eq_four_mod_eight k h,
-- exact y_eq_five_mod_eight k h,
-- exact y_eq_six_mod_eight k h,
-- exact y_eq_seven_mod_eight k h,
sorry,
end


lemma d_dvd_x_cubed : d ∣ x^3 :=
begin
have h : d ∣ y + α := euclidean_domain.gcd_dvd_left (y + α) (y - α),
have p := dvd_mul_of_dvd_right h ((y:ℤα)-α),
rw mul_comm at p,
rw ← my_factorization at p,
norm_cast at p,
rw ← sol at p,
norm_cast,
exact p,
end

lemma Norm_d_dvd_x_six : Norm d ∣ x^6 :=
begin
have h := Norm_divides (d_dvd_x_cubed sol),
have p : (Norm x)^3 = x^6, {
  unfold Norm,
  change |x ^ 2 - 2 * 0 ^ 2| ^ 3 = x ^ 6,
  nth_rewrite 1 sq,
  rw mul_zero,
  rw mul_zero,
  rw sub_zero,
  rw abs_sq,
  rw ← pow_mul,
  have : 6 = 2*3 := by dec_trivial,
  rw ← this,
},
rw pow_three at p,
rw ← Norm_mul at p,
rw ← Norm_mul at p,
rw ← pow_three at p,
rwa p at h,
end

lemma x_pow_six_odd : ¬ 2 ∣ x^6 :=
begin
by_contra,
apply x_odd sol,
exact prime.dvd_of_dvd_pow int.prime_two h,
end

lemma x_pow_six_really_odd : odd (x^6) :=
begin
have h := x_pow_six_odd sol,
rw int.two_dvd_ne_zero at h,
rwa ← int.odd_iff at h,
end
omit sol

lemma of_dvd_int {m n : ℤ} (hn : odd n) (hm : m ∣ n) : odd m :=
begin
cases hn with k hk,
cases hm with j hj,
by_contra,
rw ← int.even_iff_not_odd at h,
cases h with b hb,
rw [hj, hb, ← two_mul, add_comm] at hk,
have p := sub_eq_of_eq_add hk,
rw [mul_assoc, ← mul_sub, mul_comm] at p,
have jeff := dvd_of_mul_left_eq (b * j - k) p,
norm_num at jeff,
end

include sol

lemma Norm_d_odd : odd (Norm d) :=
begin
exact of_dvd_int (x_pow_six_really_odd sol) (Norm_d_dvd_x_six sol),
end

#eval nat.divisors 8
omit sol

lemma divisors_of_eight {k : ℤ} (h : k ∣ 8) (p : 0 ≤ k): k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 :=
begin
have hl : (0:ℤ) < 8 := by dec_trivial,
have hp := int.le_of_dvd hl h,
clear hl,
have m : k < 9,
linarith,
clear hp,
cases k with k' k'',
work_on_goal 2
{
  exfalso,
  have := int.neg_succ_of_nat_lt_zero k'',
  have chip := lt_of_lt_of_le this p,
  exact -[1+ k''].lt_irrefl chip,
},
change (k':ℤ) ∣ (8:ℕ) at h,
rw [int.coe_nat_dvd] at h,
have := (@nat.mem_divisors k' 8).2 ⟨h, dec_trivial⟩,
fin_cases this;
simp only [int.of_nat_eq_coe, int.coe_nat_bit0, algebra_map.coe_one, eq_self_iff_true, true_or, or_true],
end 
include sol


lemma Norm_d_eq_one : Norm d = 1 :=
begin
have h := Norm_d_dvd_eight,
have p := Norm_d_odd sol,
have easy : 0 ≤ Norm d := abs_nonneg _,
have q := divisors_of_eight h easy,
cases q,{
exact q,
},
cases q,{
  exfalso,
  rw q at p,
  norm_num at p,
},
cases q,{
  rw q at p,
  norm_num at p,
},
rw q at p,
norm_num at p,
end

omit sol

--Quest to find units begins

lemma norm_one_iff_unit (k : ℤα) : is_unit k ↔ Norm k = 1 :=
begin
split,{
intro h,
rw is_unit_iff_exists_inv at h,
have p : ∃ (b : ℤα), 1 = k * b := by tauto,
change k ∣ 1 at p,
have l := Norm_divides p,
have d : Norm 1 = 1 := by ring,
rw d at l,
refine int.eq_one_of_dvd_one _ l,
exact abs_nonneg _,
},
intro h,
unfold Norm at h,
rw is_unit_iff_exists_inv,
rw abs_eq at h,
{ 
  cases h,
  use (⟨k.z,-k.w⟩:ℤα),
  change (⟨k.z*k.z + 2*k.w*(-k.w), k.z*(-k.w) + k.w*k.z⟩:ℤα) = 1,
  ring_nf,
  rw h,
  refl,
  use (⟨-k.z,k.w⟩:ℤα),
  change (⟨ k.z*(-k.z) + 2*k.w*k.w, k.z*k.w + k.w*(-k.z)⟩:ℤα) = 1,
  ring_nf,
  have stu : (-1:ℤ) ≠ 0 := by dec_trivial, 
  rw ← mul_right_inj' stu at h,
  ring_nf at h,
  rw h,
  refl,
},
exact zero_le_one,
end

include sol
lemma factors_coprime : is_coprime ((y:ℤα)+α) ((y:ℤα)-α) :=
begin
 rw ← euclidean_domain.gcd_is_unit_iff,
 rw norm_one_iff_unit,
 exact Norm_d_eq_one sol,
end
omit sol

lemma sqrt_2_lb : (1:ℝ) < rt_2 :=
begin
have p : (0:ℝ) ≤  1 := zero_le_one,
have q : (0:ℝ) ≤ rt_2,{
  unfold rt_2,
  exact real.sqrt_nonneg 2,
},
rw ← abs_of_nonneg p,
rw ← abs_of_nonneg q,
rw ← sq_lt_sq,
norm_num,
end

-- lemma sqrt_2_ub : rt_2 < 2 :=
-- begin
-- have p : (0:ℝ) ≤  2 := zero_le_two,
-- have q : (0:ℝ) ≤ rt_2,{
--   unfold rt_2,
--   exact real.sqrt_nonneg 2,
-- },
-- rw ← abs_of_nonneg p,
-- rw ← abs_of_nonneg q,
-- rw ← sq_lt_sq,
-- norm_num,
-- end

lemma norm_fac (k : ℤα) : (Norm k : ℝ) = |(k.z:ℝ) + k.w*rt_2|*|(k.z:ℝ) - k.w*rt_2| :=
begin
unfold Norm,
rw ← abs_mul,
ring_nf,
rw rt_2_sq,
norm_cast,
end

lemma size_of_inv {v : ℤα} (h : is_unit v) : |(v.z:ℝ) + v.w*rt_2| = |(v.z:ℝ) - v.w*rt_2|⁻¹ :=
begin
rw norm_one_iff_unit at h,
have q : |(v.z:ℝ) - v.w*rt_2| ≠ 0,{
by_contra p,
have ll : (Norm v : ℝ) = 1 := by exact_mod_cast h,
rw norm_fac v at ll,
rw p at ll,
rw mul_zero at ll,
norm_num at ll,
},
rw ← mul_right_inj' q,
nth_rewrite 3 mul_comm,
rw inv_mul_cancel q,
rw mul_comm,
rw ← norm_fac v,
exact_mod_cast h,
end

lemma unit_not_mul_of_rt_2 {v : ℤα} (p : is_unit v) : v.z ≠ 0 :=
begin
rw norm_one_iff_unit at p,
unfold Norm at p,
by_contra,
rw [h, sq, zero_mul, zero_sub, abs_neg] at p,
have dory := sq_nonneg v.w,
have cherry : (0:ℤ)<2:=zero_lt_two,
rw ← mul_le_mul_left cherry at dory,
rw mul_zero at dory,
rw abs_of_nonneg dory at p,

have carla : (2:ℤ) ∣ 1,{
rw dvd_iff_exists_eq_mul_left,
use v.w^2,
symmetry,
rwa mul_comm,
},
norm_num at carla,
end


lemma pos_units {v : ℤα} (p : is_unit v) (h : 1 ≤ (v.z:ℝ) + v.w*rt_2) : 0 < v.z ∧ 0 ≤ v.w :=
begin
have l : 0 ≤ (v.z:ℝ) ∨ (v.z:ℝ) < 0 := le_or_lt 0 v.z,
have m : 0 ≤ (v.w:ℝ) ∨ (v.w:ℝ) < 0 := le_or_lt 0 v.w,
cases l,{
cases m,{
split,
have josh := unit_not_mul_of_rt_2 p,
have hoop : 0 ≤ v.z := by exact_mod_cast l,
rw has_le.le.lt_iff_ne hoop,
exact josh.symm,
exact_mod_cast m,
},

exfalso,
have megan := size_of_inv p,
rw norm_one_iff_unit at p,
unfold Norm at p,
have flo : (v.z:ℝ) + v.w*rt_2 < (v.z:ℝ) - v.w*rt_2,{
apply add_lt_add_left,
have q : (0:ℝ) < rt_2 := lt_trans zero_lt_one sqrt_2_lb,
rw ← neg_mul,
rw mul_lt_mul_right q,
have deborah := neg_lt_neg m,
rw neg_zero at deborah,
exact lt_trans m deborah,
},
have johnny := le_trans zero_le_one h,
have mom := lt_of_lt_of_le' flo h,

rw ← abs_eq_self at johnny,
rw ← johnny at h,
rw megan at h,
--- setup
have grandpa := lt_of_lt_of_le' mom zero_le_one,
have gran := le_of_lt (lt_of_lt_of_le' mom zero_le_one),
rw ← abs_eq_self at gran,
rw ← gran at mom,
rw ← gran at grandpa,
clear gran johnny,
--------
rw le_inv zero_lt_one grandpa at h,
rw inv_one at h,
have terry := lt_of_lt_of_le mom h,
norm_num at terry,
},
cases m,{

exfalso,
have megan := size_of_inv p,
rw norm_one_iff_unit at p,
unfold Norm at p,
have flo : (v.z:ℝ) + v.w*rt_2 < -(v.z:ℝ) + v.w*rt_2,{
apply add_lt_add_right,
have q : (0:ℝ) < rt_2 := lt_trans zero_lt_one sqrt_2_lb,
have deborah := neg_lt_neg l,
rw neg_zero at deborah,
exact lt_trans l deborah,
},
have johnny := le_trans zero_le_one h,
have mom := lt_of_lt_of_le' flo h,

rw ← abs_eq_self at johnny,
rw ← johnny at h,
have grandpa := lt_of_lt_of_le' mom zero_le_one,
have gran := le_of_lt (lt_of_lt_of_le' mom zero_le_one),
rw ← abs_eq_self at gran,
rw ← gran at mom,
rw ← gran at grandpa,
rw megan at h,
rw [← abs_neg, neg_add, ← sub_eq_add_neg, neg_neg] at grandpa,
rw [← abs_neg, neg_add, ← sub_eq_add_neg, neg_neg] at mom,
rw le_inv zero_lt_one grandpa at h,
rw inv_one at h,
have terry := lt_of_lt_of_le mom h,
norm_num at terry,
},
exfalso,
have q : (0:ℝ) ≤ rt_2,{
  unfold rt_2,
  exact real.sqrt_nonneg 2,
},

have mm := le_of_lt m,
clear m,
have ll := le_of_lt l,
clear l,
have nob := mul_le_mul_of_nonneg_right mm q,
rw zero_mul at nob,
have snob := add_le_add ll nob,
rw zero_add at snob,
have dobby := le_trans h snob,
norm_num at dobby,
end  

def next_unit : ℤα → ℤα := λ v, (⟨2*v.w - v.z, v.z - v.w⟩:ℤα)
def f_unit := (⟨1, 1⟩:ℤα)
def f_unit_inv := (⟨-1, 1⟩:ℤα)

noncomputable
def next_unit_ℝ : ℤα → ℝ  := λ v, (2*v.w - v.z) + (v.z - v.w)*rt_2

-- lemma mul_units_is_unit {u v : ℤα} (p : is_unit u) (q : is_unit v) : is_unit ((u*v):ℤα) :=
-- begin
-- rw is_unit_iff_exists_inv at p q ⊢,
-- cases q with a ha,
-- cases p with b hb,
-- use a*b,
-- rw mul_assoc,
-- nth_rewrite 1 ← mul_assoc,
-- rw ha,
-- rw one_mul,
-- exact hb,
-- end

lemma f_unit_is_unit : is_unit f_unit :=
begin
rw is_unit_iff_exists_inv,
use (⟨-1, 1⟩:ℤα),
ring_nf,
end

lemma unit_expansion (v : ℤα) : v = f_unit * next_unit v :=
begin
unfold f_unit next_unit,
change v = (⟨1*(2 * v.w - v.z) + 2*1*(v.z - v.w), 1*(v.z - v.w) + 1*(2 * v.w - v.z)⟩:ℤα),
ring_nf,
ext,
dsimp,
refl,
dsimp,
refl,
end

lemma next_unit_is_unit {v : ℤα} (h : is_unit v): is_unit (next_unit v) :=
begin
  -- apply is_unit_of_mul_is_unit_left

have q := (norm_one_iff_unit v).1 h,
unfold Norm at q,
apply (norm_one_iff_unit (next_unit v)).2,
unfold Norm next_unit,
dsimp,
ring_nf,
rwa abs_sub_comm at q,
end

lemma inductive_element_ge_one {v : ℤα} (h : is_unit v) (p : 1 + rt_2 ≤ (v.z:ℝ) + v.w*rt_2) :
1 ≤ (next_unit_ℝ v) :=
begin
unfold next_unit_ℝ,
have q : 0 < rt_2 - 1,{
  rw lt_sub_iff_add_lt',
  rw add_zero,
  exact sqrt_2_lb,
},
rw ← mul_le_mul_right q at p,
ring_nf at p,
have bob : (2:ℝ) - 1 = 1 := by norm_num,
rw [rt_2_sq, bob, add_mul, mul_assoc, ← sq, rt_2_sq, ← sub_add_eq_add_sub, mul_comm] at p,
exact p,
end

lemma components_ge_zero {v : ℤα} (h : is_unit v) (p : 1 + rt_2 ≤ (v.z:ℝ) + v.w*rt_2) :
0 < (next_unit v).z ∧ 0 ≤ (next_unit v).w :=
begin
have mm := inductive_element_ge_one h p,
have lucy := next_unit_is_unit h,
have cindy := pos_units lucy,
unfold next_unit at cindy,
dsimp at cindy,
unfold next_unit_ℝ at mm,
norm_cast at mm,
exact cindy mm,
end

-- lemma dissection_of_unit (v : ℤα): (1 + rt_2) * (next_unit_ℝ v) = (v.z:ℝ) + v.w*rt_2 :=
-- begin
-- unfold next_unit_ℝ,
-- rw [mul_add, mul_sub, sub_mul, mul_sub],
--   repeat {rw add_mul},
--   repeat {rw one_mul},
--   nth_rewrite 2 ← mul_assoc,
--   nth_rewrite 9 mul_comm,
--   rw [mul_assoc, ← sq, rt_2_sq],
--   ring_nf,
--   rw rt_2_sq,
--   ring_nf,
-- end

-- lemma inductive_element_smaller {v : ℤα} (h : is_unit v) (n : 1 + rt_2 ≤ (v.z:ℝ) + v.w*rt_2):
-- next_unit_ℝ v < (v.z:ℝ) + v.w*rt_2 :=
-- begin
-- have q : (0:ℝ) < rt_2 := lt_trans zero_lt_one sqrt_2_lb,
-- have p := add_lt_add_left q 1,
-- rw add_zero at p,
-- have mm := lt_of_lt_of_le zero_lt_one (inductive_element_ge_one h n),
-- rw ← mul_lt_mul_right mm at p,
-- rw one_mul at p,
-- rw dissection_of_unit at p,
-- exact p,
-- end

lemma units_ge_f_unit {a b : ℕ} (p : is_unit (⟨a,b⟩:ℤα)) (q : 0 < b) :
1 + rt_2 ≤ ((a:ℤ):ℝ) + ((b:ℤ):ℝ)*rt_2 :=
begin
have alice : 0 ≤ (a:ℤ) := by exact_mod_cast (zero_le a),
have ashley := unit_not_mul_of_rt_2 p,
change (a:ℤ) ≠ 0 at ashley, 
have akon := lt_iff_le_and_ne.2 ⟨alice, ashley.symm⟩,
have ben : 0 < (b:ℤ) := by exact_mod_cast q,
rw int.lt_iff_add_one_le at akon ben,
rw zero_add at akon ben,
have ben2 : 1 ≤ ((b:ℤ):ℝ) := by exact_mod_cast ben, 
have akon2 : 1 ≤ ((a:ℤ):ℝ) := by exact_mod_cast akon,
have jason : (0:ℝ) < rt_2 := lt_trans zero_lt_one sqrt_2_lb,
rw ← mul_le_mul_right jason at ben2,
rw one_mul at ben2,
exact add_le_add akon2 ben2,
end

lemma inductive_step' (a b:ℕ) (h : is_unit (⟨(a:ℤ),(b:ℤ)⟩:ℤα)) :
  ∃(n:ℕ), (⟨(a:ℤ),(b:ℤ)⟩:ℤα) = f_unit^n :=
begin
sorry,
end


lemma inductive_step :
∀(b:ℕ), (∃(a:ℕ), is_unit (⟨(a:ℤ),(b:ℤ)⟩:ℤα)) →
  (∀(a':ℕ), ((is_unit (⟨(a':ℤ),(b:ℤ)⟩:ℤα)) → ∃(n:ℕ), (⟨(a':ℤ),(b:ℤ)⟩:ℤα) = f_unit^n)) :=
begin
intro b,
induction b using nat.strong_induction_on with k hk,
dsimp at hk,

have baptist := nat.eq_zero_or_pos k,
cases baptist,{
  intro h,
  rw baptist,
  intros a ha,
  rw norm_one_iff_unit at ha,
  unfold Norm at ha,
  dsimp at ha,
  nth_rewrite 1 sq at ha,
  norm_cast at ha,
  rw [mul_zero, mul_zero, ← nat.cast_sub (zero_le (a^2)), nat.sub_zero] at ha,
  norm_cast at ha,
  have john : 1 = 1^2 := by norm_num,
  nth_rewrite 1 john at ha,
  rw sq_eq_sq (zero_le a) (zero_le_one) at ha,
  use 0,
  rw pow_zero,
  rw ha,
  refl,
},

intro h,
intros r hr,
have pastor := unit_expansion (⟨(r:ℤ),(k:ℤ)⟩:ℤα),
unfold next_unit at pastor,
dsimp at pastor,
specialize hk (r-k),
-----inequality setup
have gentle := components_ge_zero hr,
unfold next_unit at gentle,
dsimp at gentle,
have holy := gentle (units_ge_f_unit hr baptist),
have devil := holy.2,
have devil2 : k ≤ r,{
  have bb := le_of_sub_nonneg devil,
  exact_mod_cast bb,
},
have preangel : 0 < 2*(k:ℤ) - r := holy.1,
have angel : r-k < k,{
  have bbb := lt_of_sub_pos preangel,
  rw [two_mul, ← sub_lt_iff_lt_add, ← nat.cast_sub devil2] at bbb,
  exact_mod_cast bbb,
},
have angel2 : r ≤ 2*k := by exact_mod_cast le_of_lt (lt_of_sub_pos preangel),
-----
have sin := hk angel,
clear hk angel,
have god : ∃ (a : ℕ), is_unit (⟨(a:ℤ),((r-k):ℤ)⟩:ℤα),{
  use 2*k-r,
  have saint := next_unit_is_unit hr,
  unfold next_unit at saint,
  dsimp at saint,
  norm_cast at saint,
  rw ← nat.cast_sub devil2,
  exact saint,
},
rw ← nat.cast_sub devil2 at god,
have hell := sin god,
clear sin god,
specialize hell (2*k-r),
have saint := next_unit_is_unit hr,
unfold next_unit at saint,
dsimp at saint,
norm_cast at saint,
have satan := hell saint,
cases satan with n hn,
use n+1,
rw pastor,
norm_cast,
rw hn,
rw pow_add f_unit n 1,
rw mul_comm,
rw pow_one,
end

lemma equiv_ℤα (k : ℤα) : (⟨k.z,k.w⟩:ℤα) = k :=
begin
ext,
dsimp,
refl,
dsimp,
refl,
end

lemma inductive_fallout {v : ℤα} (p : is_unit v) (ha : 0 ≤ v.z) (hb : 0 ≤ v.w) :
∃(n:ℕ), v = f_unit^n :=
begin
have lady := inductive_step (int.nat_abs v.w),
have trick1 := int.nat_abs_of_nonneg hb,
have trick2 := int.nat_abs_of_nonneg ha,
rw trick1 at lady,
have boy : (∃ (a : ℕ), is_unit (⟨(a:ℤ),v.w⟩:ℤα)), {
  use int.nat_abs v.z,
  rw trick2,
  rw equiv_ℤα v,
  exact p,
},
have logan := lady boy,
clear lady boy,
specialize logan (int.nat_abs v.z),
rw trick2 at logan,
rw equiv_ℤα v at logan,
exact logan p,
end 

lemma f_unit_inv_is_unit : is_unit f_unit_inv :=
begin
rw is_unit_iff_exists_inv,
use f_unit,
ring_nf,
end

lemma f_unit_inv_for_real : ∃(m n : ℤαˣ), (m:ℤα) = f_unit ∧ (n:ℤα) = f_unit_inv ∧ n = m⁻¹ :=
begin
have h := f_unit_is_unit,
have g := f_unit_inv_is_unit,
unfold is_unit at h g,
cases g with n hn,
cases h with m hm,
use m,
use n,
split,
exact hm,
split,
exact hn,

apply eq_inv_of_mul_eq_one_left,
rw units.ext_iff,
rw units.coe_mul,
rw hn,
rw hm,
ring_nf,
end

lemma inv_of_rand_unit {v:ℤα} (p : is_unit v) :
(∃(m n: ℤαˣ), (m:ℤα) = v ∧ (n:ℤα) = (⟨-v.z, v.w⟩:ℤα) ∧ n = m⁻¹) ∨ (∃(m n: ℤαˣ), (m:ℤα) = v ∧ (n:ℤα) = (⟨v.z, -v.w⟩:ℤα) ∧ n = m⁻¹) :=
begin
have q := p,
unfold is_unit at p,
cases p with m hm,
have jane : is_unit (⟨-v.z, v.w⟩:ℤα), {
rw norm_one_iff_unit,
unfold Norm,
dsimp,
rw neg_sq,
rw norm_one_iff_unit at q,
unfold Norm at q,
exact q,
},
have bane : is_unit (⟨v.z, -v.w⟩:ℤα), {
rw norm_one_iff_unit,
unfold Norm,
dsimp,
rw neg_sq,
rw norm_one_iff_unit at q,
unfold Norm at q,
exact q,
},
cases jane with r hr,
cases bane with s hs,
rw norm_one_iff_unit at q,
unfold Norm at q,
have obv : (0:ℤ) ≤ 1 := zero_le_one, 
rw abs_eq obv at q,
clear obv,
cases q,{
  right,
  use m,
  use s,
  split,
  exact hm,
  split,
  exact hs,
  apply eq_inv_of_mul_eq_one_left,
  rw units.ext_iff,
  rw units.coe_mul,
  rw hm,
  rw hs,
  nth_rewrite 2 ← equiv_ℤα v,
  change (⟨v.z*v.z + 2*(-v.w)*v.w, v.z*v.w + (-v.w)*v.z⟩:ℤα) = 1,
  ring_nf,
  rw q,
  refl,
},

  left,
  use m,
  use r,
  split,
  exact hm,
  split,
  exact hr,
  apply eq_inv_of_mul_eq_one_left,
  rw units.ext_iff,
  rw units.coe_mul,
  rw hm,
  rw hr,
  nth_rewrite 2 ← equiv_ℤα v,
  change (⟨(-v.z)*v.z + 2*v.w*v.w, (-v.z)*v.w + v.w*v.z⟩:ℤα) = 1,
  ring_nf,
  rw [← neg_eq_iff_eq_neg, neg_sub', sub_neg_eq_add] at q,
  rw q,
  refl,
end

def f_unit' : (ℤα)ˣ := ⟨f_unit, f_unit_inv,
begin
  ext;
  dec_trivial,
end,
begin
  ext; dec_trivial,
end ⟩

lemma units_are' (v:(ℤα)ˣ) :
∃(n : ℤ), v = ((f_unit')^n : (ℤα)ˣ) ∨ v = (-(f_unit')^n : (ℤα)ˣ) :=
sorry

lemma units_are {v:ℤα} (p : is_unit v) :
∃(n : ℕ), v = (f_unit')^n ∨ v = -(f_unit')^n ∨ v = (f_unit_inv)^n ∨ v = -(f_unit_inv)^n :=
begin

have hz := le_or_lt 0 v.z,
have hw := le_or_lt 0 v.w,

cases hz,{
cases hw,{
---------------
have dolphin := inductive_fallout p hz hw,
cases dolphin with n hn,
use n,
left,
exact hn,
},

-----------------
rw ← left.neg_pos_iff at hw,
have hq := le_of_lt hw,
clear hw,
have seal : is_unit (⟨v.z, -v.w⟩:ℤα), {
rw norm_one_iff_unit,
unfold Norm,
dsimp,
rw neg_sq,
rw norm_one_iff_unit at p,
unfold Norm at p,
exact p,
},
have dolphin := inductive_fallout seal hz hq,
cases dolphin with n hn,
use n,
right,
right,

have whale := inv_of_rand_unit p,
obtain (⟨r,s,hr,hs,hi⟩ | ⟨r,s,hr,hs,hi⟩) := whale,
rw ← neg_inj at hn,
change (⟨-v.z, -(-v.w)⟩:ℤα) = -f_unit ^ n at hn,
rw neg_neg at hn,
rw ← hs at hn,
rw hi at hn,
have jelly := f_unit_inv_for_real,
cases jelly with t ht,
cases ht with l hbbb,
cases hbbb with hx hbb,
cases hbb with hy hb,

rw ← hx at hn,
have wave : r⁻¹ = -t^n := by exact_mod_cast hn,
rw inv_eq_iff_eq_inv at wave,
rw inv_neg at wave,
rw ← inv_pow at wave,
rw ← hb at wave,
have storm : (r:ℤα) = -(l:ℤα)^n := by exact_mod_cast wave,
rw hr at storm,
rw hy at storm,
right,
exact storm,
rw ← hs at hn,
rw hi at hn,
have jelly := f_unit_inv_for_real,
cases jelly with t ht,
cases ht with l hbbb,
cases hbbb with hx hbb,
cases hbb with hy hb,
rw ← hx at hn,
have wave : r⁻¹ = t^n := by exact_mod_cast hn,
rw inv_eq_iff_eq_inv at wave,
rw ← inv_pow at wave,
rw ← hb at wave,
have storm : (r:ℤα) = (l:ℤα)^n := by exact_mod_cast wave,
rw hr at storm,
rw hy at storm,
left,
exact storm,
},
-------------
cases hw, {

rw ← left.neg_pos_iff at hz,
have hq := le_of_lt hz,
clear hz,
have seal : is_unit (⟨-v.z, v.w⟩:ℤα), {
rw norm_one_iff_unit,
unfold Norm,
dsimp,
rw neg_sq,
rw norm_one_iff_unit at p,
unfold Norm at p,
exact p,
},
have dolphin := inductive_fallout seal hq hw,
cases dolphin with n hn,
use n,
right,
right,

have whale := inv_of_rand_unit p,
obtain (⟨r,s,hr,hs,hi⟩ | ⟨r,s,hr,hs,hi⟩) := whale,
rw ← hs at hn,
rw hi at hn,
have jelly := f_unit_inv_for_real,
cases jelly with t ht,
cases ht with l hbbb,
cases hbbb with hx hbb,
cases hbb with hy hb,
rw ← hx at hn,
have wave : r⁻¹ = t^n := by exact_mod_cast hn,
rw inv_eq_iff_eq_inv at wave,
rw ← inv_pow at wave,
rw ← hb at wave,
have storm : (r:ℤα) = (l:ℤα)^n := by exact_mod_cast wave,
rw hr at storm,
rw hy at storm,
left,
exact storm,
rw ← neg_inj at hn,
change (⟨-(-v.z), -v.w⟩:ℤα) = -f_unit ^ n at hn,
rw neg_neg at hn,
rw ← hs at hn,
rw hi at hn,
have jelly := f_unit_inv_for_real,
cases jelly with t ht,
cases ht with l hbbb,
cases hbbb with hx hbb,
cases hbb with hy hb,

rw ← hx at hn,
have wave : r⁻¹ = -t^n := by exact_mod_cast hn,
rw inv_eq_iff_eq_inv at wave,
rw inv_neg at wave,
rw ← inv_pow at wave,
rw ← hb at wave,
have storm : (r:ℤα) = -(l:ℤα)^n := by exact_mod_cast wave,
rw hr at storm,
rw hy at storm,
right,
exact storm,
},

-------------
rw ← left.neg_pos_iff at hz,
have hu := le_of_lt hz,
clear hz,
rw ← left.neg_pos_iff at hw,
have hq := le_of_lt hw,
clear hw,

have seal : is_unit (⟨-v.z, -v.w⟩:ℤα), {
rw norm_one_iff_unit,
unfold Norm,
dsimp,
repeat {rw neg_sq},
rw norm_one_iff_unit at p,
unfold Norm at p,
exact p,
},
have dolphin := inductive_fallout seal hu hq,
cases dolphin with n hn,
use n,
right,
left,
change -(⟨v.z,v.w⟩:ℤα) = f_unit ^ n at hn,
rw equiv_ℤα at hn,
rw ← neg_eq_iff_eq_neg,
exact hn,
end

lemma unit_assoc_cube (a : (ℤα)ˣ) :
  ∃ b : (ℤα)ˣ, a = b^3 ∨ a = f_unit' * b^3 ∨ a = f_unit'⁻¹ * b^3 :=
begin
  have kettle := units_are' a,
  obtain ⟨n, hn⟩ := kettle,
  have stove := int.div_add_mod n 3,
  have lower := int.mod_nonneg n (by dec_trivial : (3:ℤ) ≠0 ),
  have upper := int.mod_lt_of_pos n (by dec_trivial : (3:ℤ) > 0 ),
  have bowl : (-1:(ℤα)ˣ)^3 = -1, {
    rw [pow_three, ← sq, neg_one_sq, mul_one],
  },
  interval_cases using lower upper,
 
  cases hn, {
  use f_unit'^(n/3),
  rw [h,add_zero] at stove,
  left,
  rw [←zpow_of_nat, ←zpow_mul, mul_comm, int.of_nat_eq_coe, int.coe_nat_bit1, algebra_map.coe_one, stove, hn],
  },

  {
  use -f_unit'^(n/3),
  rw [h,add_zero] at stove,
  left,
  rw neg_pow,
  nth_rewrite 1 ← zpow_of_nat,
  rw ← zpow_mul,
  nth_rewrite 1 mul_comm,
  rw [int.of_nat_eq_coe, int.coe_nat_bit1, algebra_map.coe_one, stove, hn, bowl, neg_one_mul],
  },

  cases hn,
  {
  use f_unit'^(n/3),
  right,
  left,
  rw h at stove,
  rw [← zpow_of_nat, ← zpow_mul],
  nth_rewrite 1 mul_comm,
  rw [int.of_nat_eq_coe, int.coe_nat_bit1, algebra_map.coe_one, eq_sub_of_add_eq stove, mul_comm, ← zpow_add_one f_unit' (n-1), sub_add_cancel],
  exact hn,
  },

  {
  use -f_unit'^(n/3),
  right,
  left,
  rw h at stove,
  rw neg_pow,
  nth_rewrite 1 ← zpow_of_nat,
  rw ← zpow_mul,
  nth_rewrite 2 mul_comm,
  rw [int.of_nat_eq_coe, int.coe_nat_bit1, algebra_map.coe_one, eq_sub_of_add_eq stove, bowl, ← mul_assoc],
  nth_rewrite 1 mul_comm,
  rw [mul_assoc, neg_one_mul, mul_comm, ← zpow_add_one f_unit' (n-1), sub_add_cancel],
  exact hn,
  },
  
  cases hn,{
  use f_unit'^(n/3+1),
  right,
  right,
  rw h at stove,
  rw [← zpow_of_nat, ← zpow_mul],
  nth_rewrite 1 mul_comm,
  rw [int.of_nat_eq_coe, int.coe_nat_bit1, algebra_map.coe_one, mul_add, mul_one, eq_sub_of_add_eq stove, add_comm_sub, ← zpow_neg_one, ← zpow_add],
  norm_num,
  exact hn,
  },

  use -f_unit'^(n/3+1),
  right,
  right,
  rw h at stove,
  rw neg_pow,
  nth_rewrite 1 ← zpow_of_nat,
  rw ← zpow_mul,
  nth_rewrite 2 mul_comm,
  rw [int.of_nat_eq_coe, int.coe_nat_bit1, algebra_map.coe_one, mul_add,
  mul_one, eq_sub_of_add_eq stove, add_comm_sub, ← zpow_neg_one, bowl, ← mul_assoc],
  nth_rewrite 1 mul_comm,
  rw [mul_assoc, neg_one_mul, ← zpow_add],
  norm_num,
  exact hn,

end

include sol
lemma descent : ∃(k : ℤα), associated (k^3) ((y:ℤα)+α) :=
begin
have h : ((y:ℤα)+α)*(y-α) = x^3,{
rw ← my_factorization,
symmetry,
norm_cast,
ext,
exact sol,
refl,
},
exact exists_associated_pow_of_mul_eq_pow' (factors_coprime sol) h,
end

lemma descent_pro : ∃(g : ℤα), (((y:ℤα)+α) = (g^3) ∨ ((y:ℤα)+α) = f_unit'*(g^3)) ∨ ((y:ℤα)+α) = ((f_unit'.inv):ℤα) * (g^3) :=
begin
have chevy := descent sol,
have ford := unit_assoc_cube,
cases chevy with k hk,
unfold associated at hk,
cases hk with t ht,
specialize ford t,
cases ford with f hf,
cases hf with d hd,
{
  rw d at ht,
  rw units.coe_pow at ht,
  rw ← mul_pow at ht,
  use k*(f:ℤα),
  left,left,
  symmetry,
  exact ht,
},
cases hd with hj hb,
{
  rw [hj, units.coe_mul, units.coe_pow, mul_comm, mul_assoc, ← mul_pow] at ht,
  use k*(f:ℤα),
  left, right,
  rw ← ht,
  nth_rewrite 1 mul_comm,
},
rw [hb, units.coe_mul, units.coe_pow, mul_comm, mul_assoc, ← mul_pow] at ht,
use k*(f:ℤα),
right,
rw ← ht,
nth_rewrite 1 mul_comm,
refl, --what is with the inv notation?
end
omit sol

lemma element_cubed (g : ℤα) : g^3 = ⟨g.z^3 + 6*g.z*g.w^2, 3*g.z^2*g.w + 2*g.w^3⟩ :=
begin
rw pow_three,
rw mul_mule_1 g g,
nth_rewrite 0 ← equiv_ℤα g, 
rw mul_mule_2,
ext,
ring_nf, ring_nf,
end 

lemma descent_pro_1_no_sol : ¬(∃(g : ℤα), ((y:ℤα)+α) = (g^3)) :=
begin
by_contra,
cases h with g hg,
change (⟨y+0, 0+1⟩:ℤα)= g^3 at hg,
rw [ zero_add, add_zero] at hg,
rw element_cubed at hg,
ring_nf at hg,
cases hg with hf hv,
ring_nf at hv,
have q : (1:ℤ) ≠ 0 := by dec_trivial,
have p : g.w ∣ 1,
 { 
  use 2 * g.w ^ 2 + 3 * g.z ^ 2,
  rw mul_comm,
  exact hv,
 },
have g : (0 ≤ g.w) ∨ (0 ≤ -g.w), 
{
  by_contra,
  rw not_or_distrib at h,
  cases h with f hf,
  apply hf,
  linarith,
},
cases g with t ht,
have q := int.eq_one_of_dvd_one t p,
{
  rw [q, mul_one, sq, mul_one, mul_one] at hv,
  have k := sub_eq_of_eq_add' hv,
  rw (by dec_trivial : (1:ℤ) - 2 = -1) at k,
  have j : (3:ℤ) ∣ 1,
  {
    use (-(g.z^2)),
    rw mul_neg,
    rw ← neg_eq_iff_eq_neg,
    exact k,
  },
  norm_num at j,
},
have b := has_dvd.dvd.neg_left p,
have q := int.eq_one_of_dvd_one ht b,
rw neg_eq_iff_eq_neg at q,
rw [q, neg_one_sq, mul_one, mul_neg_one, neg_add] at hv,
have k := sub_eq_of_eq_add' hv,
rw [sub_neg_eq_add, (by dec_trivial : (1:ℤ) + 2 = 3), mul_comm, ← neg_mul] at k,
nth_rewrite 0 ← one_mul (3:ℤ) at k, 
rw mul_left_inj' (by dec_trivial : (3:ℤ) ≠ 0) at k,
rw ← neg_eq_iff_eq_neg at k,
have d := sq_nonneg (g.z:ℤ),
rw ← k at d,
norm_num at d,
end

lemma case_2_sol (g : ℤα) (h : (y:ℤα)+α = f_unit' * (g^3)) :
y = g.z^3 + 6*g.z^2*g.w + 6*g.z*g.w^2 + 4*g.w^3 ∧ 1 = g.z^3 + 3*g.z^2*g.w + 6*g.z*g.w^2 + 2*g.w^3 :=
begin
change (⟨y+0, 0+1⟩:ℤα) = f_unit * g^3 at h,
unfold f_unit at h,
rw [ zero_add, add_zero, element_cubed, mul_mule_2] at h,
ring_nf at h,
cases h with ha hb,
split,{
  ring_nf,
  exact ha,
},
ring_nf,
exact hb,
end

lemma case_3_sol (g : ℤα) (h : (y:ℤα)+α = f_unit'.inv * (g^3)) :
y = -g.z^3 + 6*g.z^2*g.w - 6*g.z*g.w^2 + 4*g.w^3 ∧ 1 = g.z^3 - 3*g.z^2*g.w + 6*g.z*g.w^2 - 2*g.w^3 :=
begin
change (⟨y+0, 0+1⟩:ℤα) = f_unit_inv * g^3 at h,
unfold f_unit_inv at h,
rw [ zero_add, add_zero, element_cubed, mul_mule_2] at h,
ring_nf at h,
cases h with ha hb,
split,{
  ring_nf,
  exact ha,
},
ring_nf,
exact hb,
end

end mordell
end ℤα 