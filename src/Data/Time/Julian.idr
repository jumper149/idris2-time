module Data.Time.Julian

import Data.Fin

namespace Annus

  ||| A month in a year.
  public export
  data Mensis
    = Martius
    | Aprilis
    | Maius
    | Iunius
    | Quintilis
    | Sextilis
    | September
    | October
    | November
    | December
    | Ianuarius
    | Februarius

  ||| The 7th month has been renamed after "Gaius Julius Caesar".
  public export
  Iulius : Mensis
  Iulius = Quintilis

  ||| The 8th month has been renamed after "Caesar Augustus".
  public export
  Augustus : Mensis
  Augustus = Sextilis

  public export
  dies : (bisextilis : Bool) -> Nat
  dies bisextilis = if bisextilis then 366 else 365

  ||| A day in a year.
  public export
  data Dies : (bisextilis : Bool) -> Type where
    MkDies : Fin (dies bisextilis) -> Dies bisextilis

namespace Mensis

  public export
  dies : (bisextilis : Bool) -> (mensis : Annus.Mensis) -> Nat
  dies bisextilis mensis = case mensis of
    Martius => 31
    Aprilis => 30
    Maius => 31
    Iunius => 30
    Quintilis => 31
    Sextilis => 31
    September => 30
    October => 31
    November => 30
    December => 31
    Ianuarius => 31
    Februarius => if bisextilis then 29 else 28

  ||| A day in a month.
  public export
  record Dies (bisextilis : Bool) (mensis : Annus.Mensis) where
    constructor MkDies
    getDies : Fin (dies bisextilis mensis)

namespace Dies

  ||| An hour in a day.
  public export
  record Hora where
    constructor MkHora
    getHora : Fin 24

namespace Hora

  ||| A minute in an hour.
  public export
  record Minute where
    constructor MkMinute
    getMinute : Fin 60

namespace Minute

  ||| A second in a minute.
  public export
  record Secondo where
    constructor MkSecondo
    getSecondo : Fin 60

||| The Julian day is a continuous count of days.
||| The Julian day number (JDN) is the integer assigned with that day.
||| A new day starts at noon and lasts until the next noon.
record JDN where
  constructor MkJDN
  getJDN : Integer

||| The Julian date (JD) is an instant in time.
||| It consists of a Julian day number (JDN) plus the fraction of a day, that has passed, until the next Julian day starts at noon.
record JD where
  constructor MkJD
  jdn : JDN
  fraction : Double -- TODO: This should be a rational number `x` respecting `0 <= x < 1`.
