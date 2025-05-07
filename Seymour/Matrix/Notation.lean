import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.RowCol

/-!
Custom notation for composing matrices from rows and columns.
-/

/-- Glue rows of two matrices. -/
infixl:63 " ⊟ " => Matrix.fromRows

/-- Glue columns of two matrices. -/
infixl:63 " ◫ " => Matrix.fromCols

/-- Convert vector to single-row matrix. -/
notation:64 "▬"r:81 => Matrix.replicateRow Unit r

/-- Convert vector to single-column matrix. -/
notation:64 "▮"c:81 => Matrix.replicateCol Unit c
