import Mathlib

open MeasureTheory ProbabilityTheory Metric ENNReal Set

variable {Ω 𝓧 𝓒 𝓦 E : Type}
variable [MeasureSpace Ω]
variable [PseudoEMetricSpace 𝓒] [PseudoEMetricSpace E]

noncomputable def Delta {Ω 𝓧 𝓒 𝓦 E : Type*} [PseudoEMetricSpace 𝓒] [PseudoEMetricSpace E]
  (w : 𝓦) (f : 𝓦 → 𝓒 → E) (U : 𝓧 → Set 𝓒) (X : Ω → 𝓧) (C : Ω → 𝓒) (ω : Ω) : ℝ≥0∞ :=
  ⨆ c' ∈ U (X ω), edist (f w (C ω)) (f w c')

def CoverEvent (X : Ω → 𝓧) (C : Ω → 𝓒) (U : 𝓧 → Set 𝓒) : Set Ω :=
  {ω | C ω ∈ U (X ω)}

def BoundEvent (w : 𝓦) (f : 𝓦 → 𝓒 → E) (U : 𝓧 → Set 𝓒) (X : Ω → 𝓧) (C : Ω → 𝓒) (L : NNReal) : Set Ω :=
  {ω | Delta w f U X C ω ≤ (L : ENNReal) * EMetric.diam (U (X ω))}

theorem coverage_bound
  (X : Ω → 𝓧) (C : Ω → 𝓒) (U : 𝓧 → Set 𝓒)
  (w : 𝓦) (f : 𝓦 → 𝓒 → E) (L : NNReal)
  (hf : LipschitzWith L (f w))
  (α : ENNReal)
  (h_cov : volume (CoverEvent X C U) ≥ 1 - α) :
  volume (BoundEvent w f U X C L) ≥ 1 - α := by
  -- show CoverEvent ⊆ BoundEvent
  have hset : CoverEvent X C U ⊆ BoundEvent w f U X C L := by
    intro ω hω
    -- unfold events
    -- hω : C ω ∈ U (X ω)
    show Delta w f U X C ω ≤ (L : ENNReal) * EMetric.diam (U (X ω))
    unfold Delta
    -- bound the supremum by bounding each term
    refine iSup₂_le ?_
    intro c' hc'
    -- Lipschitz bound, then diam bound
    refine le_trans (hf.edist_le_mul (C ω) c') ?_
    -- edist (C ω) c' ≤ diam since both are in U (X ω)
    have hdiam : edist (C ω) c' ≤ EMetric.diam (U (X ω)) :=
      EMetric.edist_le_diam_of_mem hω hc'
    -- multiply both sides by L
    exact mul_le_mul_right hdiam (L : ENNReal)

  -- now use monotonicity of measure + the given lower bound
  have hmono : volume (CoverEvent X C U) ≤ volume (BoundEvent w f U X C L) :=
    MeasureTheory.measure_mono hset

  exact le_trans h_cov hmono
