module

public import BlockBand.Native.ErdosRiabov.Prop.RegProps

/-!
# Regularized chains: site-operator algebra and the commutator identity

Algebra of kernel actions on functions of `k` sites, and the commutator identity between the
regularization `𝒟` and the generator of the saturated chains. Functions of `k` sites
`f : (Fin k → Fin N) → ℂ` (`CircFun N k`) and `ℂ`-linear operators on
them (`Module.End`). Coordinates are 0-based; `x[i ↦ c] = Function.update x i c`.

* `circSlot i K`: `K^{(i)} f(x) = Σ_c K(x_i, c) f(x[i ↦ c])`; `circGen K = Σ_i K^{(i)}` (with
  `K = T̂_s` this is `T̂_s^{⊕k}`, the generator of the saturated chains).
* `circDiagE a j`: `E f(x) = 𝟙(x_a = x_j) Σ_b f(x[j ↦ b])`, and ER's `𝒟 = 1 - E`
  (`circDiag a j`; ER: `𝒟[f](x,y) = Σ_b (δ_{yb} - δ_{xy}) f(x,b)` on the pair `(x_a, x_j)`).
* `circRing j a K = K^{(j)} 𝒟_{a,j}`; for `K = T̂_t` it is `Propagator.ringOp` (`Θ̊^{(j)}_t`,
  anchor `a`): `ringOp_eq_circRing`.
* `circExtra K a j`: ER's extra forcing operator,
  `F̃ f(x) = K(x_a, x_j) (Σ_b f(x[a ↦ x_j][j ↦ b]) + Σ_b f(x[j ↦ b]))`.
* **`circDiagE_commutator`**: for a symmetric `K` with constant row sums and
  `a ≠ j`, `E (K^{(a)} + K^{(j)}) = (K^{(a)} + K^{(j)}) E - F̃ + E F̃`, i.e.
  `[𝒟, K^{(a)} + K^{(j)}] = 𝒟 F̃`.
* **`circRing_mul_circGen`** (one ring, short chains): for `Commute K K'`, `K'` symmetric with
  constant row sums, `a ≠ j`:
  `circRing j a K * circGen K' = circGen K' * circRing j a K + circRing j a K * F̃'_{a,j}`.
* **`circRing2_mul_circGen`** (two rings on disjoint pairs, long chains): with `𝒰 = R₁ R₂`,
  `𝒰 * circGen K' = circGen K' * 𝒰 + 𝒰 * (F̃'_{a₁,j₁} + F̃'_{a₂,j₂})`
  (ER `[𝒟⊗𝒟, 𝒞⊕𝒞] = 𝒟⊗[𝒟,𝒞] + [𝒟,𝒞]⊗𝒟`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open Function
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.External.ErdosRiabov (semicircleM)
open scoped ComplexConjugate

variable {N k : ℕ}

/-- Complex functions of `k` sites in `Fin N`. -/
abbrev CircFun (N k : ℕ) : Type := (Fin k → Fin N) → ℂ

/-!
### The operators
-/

/-- One-coordinate kernel action `K^{(i)} f(x) = Σ_c K(x_i, c) f(x[i ↦ c])`. -/
def circSlot (i : Fin k) (K : Matrix (Fin N) (Fin N) ℂ) : Module.End ℂ (CircFun N k) where
  toFun f x := ∑ c, K (x i) c * f (update x i c)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring

theorem circSlot_apply (i : Fin k) (K : Matrix (Fin N) (Fin N) ℂ) (f : CircFun N k)
    (x : Fin k → Fin N) : circSlot i K f x = ∑ c, K (x i) c * f (update x i c) := rfl

/-- `E f(x) = 𝟙(x_a = x_j) Σ_b f(x[j ↦ b])` (the `δ_{xy}` part of ER's `𝒟`). -/
def circDiagE (a j : Fin k) : Module.End ℂ (CircFun N k) where
  toFun f x := if x a = x j then ∑ b, f (update x j b) else 0
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    split_ifs <;> simp [Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [Finset.mul_sum]

theorem circDiagE_apply (a j : Fin k) (f : CircFun N k) (x : Fin k → Fin N) :
    circDiagE a j f x = if x a = x j then ∑ b, f (update x j b) else 0 := rfl

/-- ER's `𝒟 = 1 - E` on the pair of coordinates `(a, j)`. -/
def circDiag (a j : Fin k) : Module.End ℂ (CircFun N k) := 1 - circDiagE a j

/-- ER's extra forcing operator on the pair `(a, j)`:
`F̃ f(x) = K(x_a, x_j) (Σ_b f(x[a ↦ x_j][j ↦ b]) + Σ_b f(x[j ↦ b]))`. -/
def circExtra (K : Matrix (Fin N) (Fin N) ℂ) (a j : Fin k) : Module.End ℂ (CircFun N k) where
  toFun f x := K (x a) (x j) *
    (∑ b, f (update (update x a (x j)) j b) + ∑ b, f (update x j b))
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem circExtra_apply (K : Matrix (Fin N) (Fin N) ℂ) (a j : Fin k) (f : CircFun N k)
    (x : Fin k → Fin N) : circExtra K a j f x = K (x a) (x j) *
      (∑ b, f (update (update x a (x j)) j b) + ∑ b, f (update x j b)) := rfl

/-- The generator `K^{⊕k} = Σ_i K^{(i)}`. -/
def circGen (K : Matrix (Fin N) (Fin N) ℂ) : Module.End ℂ (CircFun N k) := ∑ i, circSlot i K

/-- One regularized ring `K^{(j)} 𝒟_{a,j}` (ER `Θ̊^{(j)} = Θ^{(j)} ∘ 𝒟^{(j)}`). -/
def circRing (j a : Fin k) (K : Matrix (Fin N) (Fin N) ℂ) : Module.End ℂ (CircFun N k) :=
  circSlot j K * circDiag a j

/-!
### Commutation of one-coordinate actions
-/

theorem circSlot_comm {i i' : Fin k} (hne : i ≠ i') (K K' : Matrix (Fin N) (Fin N) ℂ) :
    circSlot i K * circSlot i' K' = circSlot i' K' * circSlot i K := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, circSlot_apply, update_of_ne hne, update_of_ne hne.symm,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun c _ => ?_
  rw [update_comm hne]
  ring

theorem circSlot_mul_same (i : Fin k) (K K' : Matrix (Fin N) (Fin N) ℂ) :
    circSlot i K * circSlot i K' = circSlot i (K * K') := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, circSlot_apply, update_self, update_idem, Finset.mul_sum,
    Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun c _ => by ring

theorem circSlot_comm_same (i : Fin k) {K K' : Matrix (Fin N) (Fin N) ℂ} (h : Commute K K') :
    circSlot i K * circSlot i K' = circSlot i K' * circSlot i K := by
  rw [circSlot_mul_same, circSlot_mul_same, h.eq]

theorem circSlot_mul_circGen (i : Fin k) {K K' : Matrix (Fin N) (Fin N) ℂ} (h : Commute K K') :
    circSlot i K * circGen K' = circGen K' * circSlot i K := by
  unfold circGen
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  by_cases hii : i = i'
  · subst hii
    exact circSlot_comm_same i h
  · exact circSlot_comm hii K K'

theorem circDiagE_mul_circSlot {a j i : Fin k} (hia : i ≠ a) (hij : i ≠ j)
    (K : Matrix (Fin N) (Fin N) ℂ) :
    circDiagE a j * circSlot i K = circSlot i K * circDiagE a j := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, circSlot_apply, circDiagE_apply, update_of_ne hij,
    update_of_ne hia.symm, update_of_ne hij.symm]
  split_ifs with h
  · rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    rw [update_comm hij.symm]
  · simp

/-!
### The commutator identity `[𝒟, K^{(a)} + K^{(j)}] = 𝒟 F̃`
-/

/-- **The commutator identity** (VS form): for `K` symmetric with constant row sums `r` and
`a ≠ j`, `E (K^{(a)} + K^{(j)}) = (K^{(a)} + K^{(j)}) E - F̃ + E F̃`, equivalently
`[𝒟, K^{(a)} + K^{(j)}] = 𝒟 F̃` with `𝒟 = 1 - E`. -/
theorem circDiagE_commutator {K : Matrix (Fin N) (Fin N) ℂ} (hK : ∀ u v, K u v = K v u)
    {r : ℂ} (hr : ∀ u, ∑ v, K u v = r) {a j : Fin k} (haj : a ≠ j) :
    circDiagE a j * (circSlot a K + circSlot j K) =
      (circSlot a K + circSlot j K) * circDiagE a j - circExtra K a j +
        circDiagE a j * circExtra K a j := by
  have hc : ∀ c, ∑ b, K b c = r := fun c => by
    rw [← hr c]
    exact Finset.sum_congr rfl fun b _ => hK b c
  refine LinearMap.ext fun f => funext fun x => ?_
  set G : Fin N → ℂ := fun c => ∑ b, f (update (update x a c) j b) with hG
  set g : ℂ := ∑ b, f (update x j b) with hg
  have h1 : ∑ c, K (x a) c * (if c = x j then G c else 0) = K (x a) (x j) * G (x j) := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h2 : ∑ c, K (x j) c * (if x a = c then g else 0) = K (x j) (x a) * g := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hEx : ∀ b, circExtra K a j f (update x j b) = K (x a) b * (G b + g) := by
    intro b
    rw [circExtra_apply, update_of_ne haj, update_self, update_comm haj.symm]
    simp only [update_idem, G, g]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Pi.add_apply,
    Pi.sub_apply, circSlot_apply, circDiagE_apply, update_of_ne haj, update_of_ne haj.symm,
    update_self, update_idem]
  rw [h1, h2]
  simp only [hEx]
  rw [circExtra_apply]
  change _ = K (x a) (x j) * G (x j) + K (x j) (x a) * g - K (x a) (x j) * (G (x j) + g) + _
  split_ifs with h
  · have e1 : ∑ b, (∑ c, K (x a) c * f (update (update x j b) a c) +
        ∑ c, K b c * f (update x j c)) = ∑ c, K (x a) c * G c + r * g := by
      rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun b c => K b c * f (update x j c))]
      congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hG, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [update_comm haj.symm]
      · simp only [← Finset.sum_mul, hc, hg, Finset.mul_sum]
    have e2 : ∑ b, K (x a) b * (G b + g) = ∑ c, K (x a) c * G c + r * g := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hr]
    rw [e1, e2, hK (x j) (x a)]
    ring
  · rw [hK (x j) (x a)]
    ring

/-!
### Rings and the generator
-/

private theorem circSum_split {M : Type*} [AddCommMonoid M] {a j : Fin k} (haj : a ≠ j)
    (g : Fin k → M) : ∑ i, g i = g a + g j + ∑ i ∈ (Finset.univ.erase a).erase j, g i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨haj.symm, Finset.mem_univ j⟩), add_assoc]

theorem circDiagE_mul_circGen {K : Matrix (Fin N) (Fin N) ℂ} (hK : ∀ u v, K u v = K v u)
    {r : ℂ} (hr : ∀ u, ∑ v, K u v = r) {a j : Fin k} (haj : a ≠ j) :
    circDiagE a j * circGen K =
      circGen K * circDiagE a j - circExtra K a j + circDiagE a j * circExtra K a j := by
  have hrest : ∑ i ∈ (Finset.univ.erase a).erase j, circDiagE a j * circSlot i K =
      ∑ i ∈ (Finset.univ.erase a).erase j, circSlot i K * circDiagE a j := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hia : i ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    exact circDiagE_mul_circSlot hia hij K
  have hkey := circDiagE_commutator hK hr haj
  unfold circGen
  rw [Finset.mul_sum, Finset.sum_mul, circSum_split haj (fun i => circDiagE a j * circSlot i K),
    circSum_split haj (fun i => circSlot i K * circDiagE a j), hrest]
  rw [mul_add] at hkey
  rw [hkey, add_mul]
  abel

theorem circDiag_mul_circGen {K : Matrix (Fin N) (Fin N) ℂ} (hK : ∀ u v, K u v = K v u)
    {r : ℂ} (hr : ∀ u, ∑ v, K u v = r) {a j : Fin k} (haj : a ≠ j) :
    circDiag a j * circGen K = circGen K * circDiag a j + circDiag a j * circExtra K a j := by
  unfold circDiag
  rw [sub_mul, one_mul, circDiagE_mul_circGen hK hr haj, mul_sub, mul_one, sub_mul, one_mul]
  abel

/-- **One ring** (short chains): for `Commute K K'`, `K'` symmetric with
constant row sums and `a ≠ j`: `R K'^{⊕k} = K'^{⊕k} R + R F̃'`, `R = circRing j a K`. -/
theorem circRing_mul_circGen {K K' : Matrix (Fin N) (Fin N) ℂ} (hKK : Commute K K')
    (hK : ∀ u v, K' u v = K' v u) {r : ℂ} (hr : ∀ u, ∑ v, K' u v = r) {a j : Fin k}
    (haj : a ≠ j) :
    circRing j a K * circGen K' =
      circGen K' * circRing j a K + circRing j a K * circExtra K' a j := by
  unfold circRing
  rw [mul_assoc, circDiag_mul_circGen hK hr haj, mul_add, ← mul_assoc,
    circSlot_mul_circGen j hKK, mul_assoc, mul_assoc]

/-!
### Disjoint pairs
-/

theorem circExtra_mul_circSlot {a j i : Fin k} (hia : i ≠ a) (hij : i ≠ j)
    (K K' : Matrix (Fin N) (Fin N) ℂ) :
    circExtra K a j * circSlot i K' = circSlot i K' * circExtra K a j := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, circSlot_apply, circExtra_apply, update_of_ne hij,
    update_of_ne hia, update_of_ne hia.symm, update_of_ne hij.symm, update_comm hij.symm,
    update_comm hia.symm]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem circExtra_mul_circDiagE {a j a' j' : Fin k} (h1 : a' ≠ a) (h2 : a' ≠ j) (h3 : j' ≠ a)
    (h4 : j' ≠ j) (K : Matrix (Fin N) (Fin N) ℂ) :
    circExtra K a j * circDiagE a' j' = circDiagE a' j' * circExtra K a j := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, circDiagE_apply, circExtra_apply, update_of_ne h1,
    update_of_ne h2, update_of_ne h3, update_of_ne h4, update_of_ne h3.symm,
    update_of_ne h4.symm, update_comm h4.symm,
    update_comm h3.symm]
  split_ifs with h
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  · simp

theorem circExtra_mul_circRing {a j a' j' : Fin k} (h1 : a' ≠ a) (h2 : a' ≠ j) (h3 : j' ≠ a)
    (h4 : j' ≠ j) (K K' : Matrix (Fin N) (Fin N) ℂ) :
    circExtra K a j * circRing j' a' K' = circRing j' a' K' * circExtra K a j := by
  unfold circRing circDiag
  rw [← mul_assoc, circExtra_mul_circSlot h3 h4, mul_assoc, mul_sub, mul_one,
    circExtra_mul_circDiagE h1 h2 h3 h4, mul_assoc, sub_mul, one_mul]

/-- **Two rings on disjoint pairs** (long chains): with
`𝒰 = R₁ R₂`, `R_i = circRing j_i a_i K`, `𝒰 K'^{⊕k} = K'^{⊕k} 𝒰 + 𝒰 (F̃'_{a₁,j₁} + F̃'_{a₂,j₂})`. -/
theorem circRing2_mul_circGen {K K' : Matrix (Fin N) (Fin N) ℂ} (hKK : Commute K K')
    (hK : ∀ u v, K' u v = K' v u) {r : ℂ} (hr : ∀ u, ∑ v, K' u v = r) {a₁ j₁ a₂ j₂ : Fin k}
    (h₁ : a₁ ≠ j₁) (h₂ : a₂ ≠ j₂) (d1 : a₂ ≠ a₁) (d2 : a₂ ≠ j₁) (d3 : j₂ ≠ a₁)
    (d4 : j₂ ≠ j₁) :
    circRing j₁ a₁ K * circRing j₂ a₂ K * circGen K' =
      circGen K' * (circRing j₁ a₁ K * circRing j₂ a₂ K) +
        circRing j₁ a₁ K * circRing j₂ a₂ K * (circExtra K' a₁ j₁ + circExtra K' a₂ j₂) := by
  rw [mul_assoc, circRing_mul_circGen hKK hK hr h₂, mul_add, ← mul_assoc,
    circRing_mul_circGen hKK hK hr h₁, add_mul, mul_assoc (circRing j₁ a₁ K) (circExtra K' a₁ j₁),
    circExtra_mul_circRing d1 d2 d3 d4, mul_add]
  simp only [mul_assoc]
  abel

/-!
### `ringOp`
-/

/-- `Propagator.ringOp` is `circRing` with `K = T̂_t` (`a ≠ j`). -/
theorem ringOp_eq_circRing (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) {j a : Fin k}
    (haj : a ≠ j) (f : CircFun N k) :
    Propagator.ringOp S z t j a f =
      circRing j a (vsKernel S (semicircleM z) (conj (semicircleM z)) t) f := by
  funext x
  simp only [Propagator.ringOp, circRing, circDiag, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, circSlot_apply, circDiagE_apply, Pi.sub_apply, update_of_ne haj,
    update_self, update_idem, Propagator.vsThetaRing_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]
  congr 1
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]

end BlockBand.Native.ErdosRiabov.Circ
