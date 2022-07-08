module Data.Time.Calendar.Julian

import Data.Fin

||| The Julian day is a continuous count of days.
||| The Julian day number (JDN) is the integer assigned with that day.
||| A new day starts at noon and lasts until the next noon.
public export
record JDN where
  constructor MkJDN
  getJDN : Nat

||| The Julian date (JD) is an instant in time.
||| It consists of a Julian day number (JDN) plus the fraction of a day, that has passed, until the next Julian day starts at noon.
public export
record JD where
  constructor MkJD
  getJDN : JDN
  getFraction : Double -- TODO: This should be a rational number `x` respecting `0 <= x < 1`.

||| A year in the Julian calendar.
||| This represents the "anno domini" (AD).
||| Usually the first year is labeled one, but here we use zero as our first year.
public export
record Annus where
  constructor MkAnnus
  getAnnus : Nat

||| Every 4th year is a leap year.
bisextus : Annus -> Bool
bisextus annus =
  case getAnnus annus of
    Z => False
    S Z => False
    S (S Z) => False
    S (S (S Z)) => True
    S (S (S (S n))) => bisextus $ MkAnnus n

bisextusProof : {n : Nat} -> bisextus (MkAnnus (S (S (S (S n))))) = bisextus (MkAnnus n)
bisextusProof = Refl

namespace Annus

  ||| A month in a year.
  public export
  data Mensis
    = Ianuarius
    | Februarius
    | Martius
    | Aprilis
    | Maius
    | Iunius
    | Quintilis
    | Sextilis
    | September
    | October
    | November
    | December

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

  ||| A real day in the history of the earth after 1AD.
  public export
  record Date where
    constructor MkDate
    annus : Annus
    dies : Dies (bisextus annus)

  public export
  toJDN : (date : Date) ->
          JDN
  toJDN date with (date)
    _ | MkDate (MkAnnus (S (S (S (S n))))) d =
      let recJDN = toJDN $ MkDate (MkAnnus n) d
      in MkJDN $ dies False + dies False + dies False + dies True + getJDN recJDN
    _ | MkDate (MkAnnus Z) d = MkJDN . finToNat $ getDies d
    _ | MkDate (MkAnnus (S Z)) d =
      MkJDN $ dies False + finToNat (getDies d)
    _ | MkDate (MkAnnus (S (S Z))) d =
      MkJDN $ dies False + dies False + finToNat (getDies d)
    _ | MkDate (MkAnnus (S (S (S Z)))) d =
      MkJDN $ dies False + dies False + dies False + finToNat (getDies d)

  -- TODO
  public export
  fromJDN : (jdn : JDN) ->
            Date
  fromJDN jdn =
    case getJDN jdn of
      Z => MkDate (MkAnnus Z) (MkDies FZ)
      _ => ?from_JDN_rhs

  -- TODO
  proof1 : x = fromJDN (toJDN x)
  proof2 : x = toJDN (fromJDN x)

namespace Mensis

  public export
  dies : (bisextilis : Bool) -> (mensis : Mensis) -> Nat
  dies bisextilis mensis = case mensis of
    Ianuarius => 31
    Februarius => if bisextilis then 29 else 28
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

  ||| A day in a month.
  public export
  record Dies (bisextilis : Bool) (mensis : Mensis) where
    constructor MkDies
    getDies : Fin (dies bisextilis mensis)

  public export
  record Date where
    constructor MkDate
    annus : Annus
    mensis : Mensis
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

-- TODO
public export
dateAnnusToMensis : (date : Annus.Date) ->
                    Mensis.Date
dateAnnusToMensis date = ?dateAnnusToMensis_rhs

-- TODO
public export
dateMensisToAnnus : (date : Mensis.Date) ->
                    Annus.Date
dateMensisToAnnus date = ?dateMensisToAnnus_rhs

-- TODO
proof1 : x = dateAnnusToMensis (dateMensisToAnnus x)
proof2 : x = dateMensisToAnnus (dateAnnusToMensis x)
