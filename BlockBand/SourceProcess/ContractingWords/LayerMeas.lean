module

public import BlockBand.SourceProcess.ContractingWords.LayerWord
public import BlockBand.SourceProcess.CompleteSourceGap.IntegrableSep
public import BlockBand.SourceProcess.FullSourceStops.WordValue

/-!
# Joint measurability of the one-step update (old state, fresh layer)

* `measurable_newProd_comp`: `newProd` of measurable letters, transport, row and separators;
* `measurable_freshTwoPortSchur_comp`: `(𝕏, fresh) ↦ 𝕏₊` jointly, not only for fixed `𝕏`;
* `measurable_layerZ`: `(𝕏, A, fresh) ↦ newProd A c N D (sepOf 𝕏₊) Zs` along measurable inputs.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.FullSourceStops
open scoped Matrix.Norms.L2Operator

variable {W nT nI : ℕ} {α : Type*} [MeasurableSpace α]

theorem measurable_matrix_trace' {n : Type*} [Fintype n] {f : α → Matrix n n ℂ}
    (hf : Measurable f) : Measurable fun a => (f a).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.measurable_sum _ fun i _ => hf.eval_matrix

theorem measurable_matrix_list_prod {n : Type*} [Fintype n] [DecidableEq n] {β : Type*}
    (L : List β) {f : β → α → Matrix n n ℂ} (hf : ∀ x ∈ L, Measurable (f x)) :
    Measurable fun a => (L.map fun x => f x a).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact measurable_matrix_mul' (hf x (List.mem_cons_self ..))
      (ih fun y hy => hf y (List.mem_cons_of_mem _ hy))

theorem measurable_newProd_comp {A : α → TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (c : TraceLetter nT nI → ℝ) {N : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {D : α → Matrix (Fin W) (Fin 2 × Fin W) ℂ}
    {S : α → Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hA : ∀ ℓ, Measurable fun a => A a ℓ) (hN : Measurable N) (hD : Measurable D)
    (hS : ∀ σ, Measurable fun a => S a σ) (Zs : List (TraceWord nT nI)) :
    Measurable fun a => newProd (A a) c (N a) (D a) (S a) Zs := by
  have hDD : Measurable fun a => (D a)ᴴ * D a :=
    measurable_matrix_mul' (measurable_matrix_conjTranspose' hD) hD
  have hlet : ∀ x : TraceLetter nT nI × Separator, Measurable fun a =>
      ((N a)ᴴ * A a x.1 * N a + (c x.1 : ℂ) • ((D a)ᴴ * D a)) * S a x.2 := fun x =>
    measurable_matrix_mul' ((measurable_matrix_mul' (measurable_matrix_mul'
      (measurable_matrix_conjTranspose' hN) (hA x.1)) hN).add (measurable_matrix_smul _ hDD))
      (hS x.2)
  have hw : ∀ w : TraceWord nT nI, Measurable fun a => newWord (A a) c (N a) (D a) (S a) w :=
    fun w => measurable_matrix_trace' (measurable_matrix_list_prod w fun x _ => hlet x)
  simp only [newProd]
  induction Zs with
  | nil => simp
  | cons w Zs ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hw w).mul ih

theorem measurable_freshTwoPortSchur_comp (E : ℝ)
    {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ω : α → LayerSample W .oneBlockOnePort}
    (hXX : Measurable XX) (hω : Measurable ω) :
    Measurable fun a => freshTwoPortSchur E (XX a) (ω a) := by
  have hA0 : Measurable fun ω : LayerSample W .oneBlockOnePort => ω.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have hB0 : Measurable fun ω : LayerSample W .oneBlockOnePort => ω.2 0 0 :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp measurable_snd)
  have hA : Measurable fun a => (ω a).1 0 := hA0.comp hω
  have hB : Measurable fun a => (ω a).2 0 0 := hB0.comp hω
  have hBs := measurable_matrix_conjTranspose' hB
  have hP : ∀ i j : Fin 2, Measurable fun a => portBlock (XX a) i j :=
    FullSource.measurable_portBlock_comp hXX
  have hG : Measurable fun a => ((ω a).1 0 - (E : ℂ) • 1 - portBlock (XX a) 0 0)⁻¹ :=
    measurable_matrix_inv.comp ((hA.sub measurable_const).sub (hP 0 0))
  exact measurable_ofPortBlocks (measurable_matrix_mul' (measurable_matrix_mul' hBs hG) hB)
    (measurable_matrix_mul' (measurable_matrix_mul' hBs hG) (hP 0 1)).neg
    (measurable_matrix_mul' (measurable_matrix_mul' (hP 1 0) hG) hB).neg
    ((hP 1 1).add (measurable_matrix_mul' (measurable_matrix_mul' (hP 1 0) hG) (hP 0 1)))

/-- **The layer value along measurable inputs.** -/
theorem measurable_layerZ (b E : ℝ)
    {A : α → TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (c : TraceLetter nT nI → ℝ) {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {ω : α → LayerSample W .oneBlockOnePort} (hA : ∀ ℓ, Measurable fun a => A a ℓ)
    (hXX : Measurable XX) (hω : Measurable ω) (Zs : List (TraceWord nT nI)) :
    Measurable fun a => newProd (A a) c (freshTransport b E (XX a) (ω a)) (freshD b E (XX a) (ω a))
      (sepOf b E (freshTwoPortSchur E (XX a) (ω a))) Zs :=
  measurable_newProd_comp c hA (FullSource.measurable_freshTransport_comp b E hXX hω)
    (FullSource.measurable_freshD_comp b E hXX hω)
    (fun σ => (measurable_sepOf b E σ).comp (measurable_freshTwoPortSchur_comp E hXX hω)) Zs

end BlockBand.SourceProcess.ContractingWords
