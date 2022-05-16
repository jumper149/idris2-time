module Data.Time.Julian

import Data.Fin

||| The Julian day is a continuous count of days.
||| The Julian day number (JDN) is the integer assigned with that day.
||| A new day starts at noon and lasts until the next noon.
record JDN where
  constructor MkJDN
  getJDN : Nat

||| The Julian date (JD) is an instant in time.
||| It consists of a Julian day number (JDN) plus the fraction of a day, that has passed, until the next Julian day starts at noon.
record JD where
  constructor MkJD
  getJDN : JDN
  getFraction : Double -- TODO: This should be a rational number `x` respecting `0 <= x < 1`.

||| A year in the Julian calendar.
||| Usually the first year is labeled one, but here we use zero as our first year.
public export
record Annus where
  constructor MkAnnus
  getAnnus : Nat

||| Every 4th year is a leap year.
bisextus : Annus -> Bool
bisextus annus =
  case getAnnus annus of
    Z => True
    S Z => False
    S (S Z) => False
    S (S (S Z)) => False
    S (S (S (S n))) => bisextus $ MkAnnus n

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
  record Dies (bisextilis : Bool) where
    constructor MkDies
    getDies : Fin (dies bisextilis)

  public export
  record Date where
    constructor MkDate
    annus : Annus
    dies : Dies (bisextus annus)

  public export
  toJDN : (date : Date) ->
          JDN
  toJDN date =
    case getAnnus date.annus of
      Z => MkJDN . finToNat $ getDies date.dies
      S Z => MkJDN $ dies False + getJDN (toJDN $ MkDate date.annus date.dies)
      S (S Z) => MkJDN $ dies False + dies False + getJDN (toJDN $ MkDate date.annus date.dies)
      S (S (S Z)) => MkJDN $ dies False + dies False + dies False + getJDN (toJDN $ MkDate date.annus date.dies)
      S (S (S (S n))) => MkJDN $ dies False + dies False + dies False + dies True + getJDN (toJDN $ MkDate date.annus date.dies)

  -- TODO
  public export
  fromJDN : (jdn : JDN) ->
            Date
  fromJDN jdn = ?fromJDN_rhs

  -- TODO
  proof1 : x = fromJDN (toJDN x)
  proof2 : x = toJDN (fromJDN x)

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

  public export
  record Date where
    constructor MkDate
    annus : Annus
    mensis : Annus.Mensis
    dies : Dies (bisextus annus) mensis

  -- TODO
  public export
  toJDN : (date : Mensis.Date) -> -- TODO: Why is it necessary to qualify the type of `date`.
          JDN
  toJDN date = ?toJDN_rhs

  -- TODO
  public export
  fromJDN : (jdn : JDN) ->
            Mensis.Date
  fromJDN jdn = ?fromJDN_rhs

  -- TODO
  proof1 : x = Mensis.fromJDN (Mensis.toJDN x)
  proof2 : x = Mensis.toJDN (Mensis.fromJDN x)

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
