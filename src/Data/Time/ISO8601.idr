module Data.Time.ISO8601

import Data.Fin
import Data.Time

||| Years before 1583 are only to be used in agreement.
public export
record Year where
  constructor MkYear
  getYear : Fin 10000
