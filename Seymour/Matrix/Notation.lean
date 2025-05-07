import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.RowCol

/-!
Custom notation for composing matrices from rows and columns.
-/

/-- Glue rows of two matrices. -/
infixl:63 " ⊟ " => Matrix.fromRows

/-- Glue cols of two matrices. -/
infixl:63 " ◫ " => Matrix.fromCols

/-- Convert vector to a single-row matrix. -/
notation:64 "▬"r:81 => Matrix.replicateRow Unit r

/-- Convert vector to a single-col matrix. -/
notation:64 "▮"c:81 => Matrix.replicateCol Unit c
