

-- /-! ## Conversion from and to standard representation -/

-- /-- Matrix 3-sum of standard representations. -/
-- def MatrixSum3.fromStandardRepr {α : Type} [DecidableEq α] {F : Type} {Sₗ Sᵣ : StandardRepr α F} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
--     (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) :
--     MatrixSum3 (Sₗ.X \ {x₀, x₁}).Elem (Sₗ.Y \ {y₀, y₁, y₂}).Elem (Sᵣ.X \ {x₀, x₁, x₂}).Elem (Sᵣ.Y \ {y₀, y₁}).Elem F where
--   x₂ := sorry
--   y₂ := sorry
--   Aₗ := sorry
--   Dₗ := sorry
--   D₀ₗ := sorry
--   D₀ᵣ := sorry
--   Dᵣ := sorry
--   Aᵣ := sorry

-- /-- Conversion of matrix 3-sum to standard representation. -/
-- def MatrixSum3.toStandardRepr {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
--     [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
--     (x₀ x₁ x₂ y₀ y₁ y₂ : α)
--     -- todo: require all necessary sets to be disjoint
--     {F : Type} [Field F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
--     StandardRepr α F where
--   X := Xₗ ∪ {x₀, x₁} ∪ Xᵣ
--   Y := Yₗ ∪ {y₀, y₁} ∪ Yᵣ
--   hXY := sorry
--   B := (by
--     let := S.matrix;
--     exact (S.matrix.toMatrixUnionUnion).toMatrixUnionUnion)
--   decmemX := inferInstance
--   decmemY := inferInstance

-- /-- Matrix-level 3-sum of standard representations. -/
-- def StandardRepr.sum3 {α : Type} [DecidableEq α] {F : Type} {Sₗ Sᵣ : StandardRepr α F} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
--     (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) :
--     MatrixSum3 (Sₗ.X \ {x₀, x₁}).Elem (Sₗ.Y \ {y₀, y₁, y₂}).Elem (Sᵣ.X \ {x₀, x₁, x₂}).Elem (Sᵣ.Y \ {y₀, y₁}).Elem F :=
--   MatrixSum3.fromStandardRepr hXX hYY

-- /-- Standard representation-level 3-sum of standard representations. -/
-- def StandardRepr.standardReprSum3 {α : Type} [DecidableEq α] {F : Type} {Sₗ Sᵣ : StandardRepr α F} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
--     (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) :
--     StandardRepr α F :=
--   (MatrixSum3.fromStandardRepr hXX hYY).toStandardRepr x₀ x₁ x₂ y₀ y₁ y₂


-- /-! ## Correctness on standard representation level -/

-- --todo: add
