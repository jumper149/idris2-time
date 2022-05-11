module Data.Time

import Data.Fin

namespace Year

  public export
  data Month
    = January
    | February
    | March
    | April
    | May
    | June
    | July
    | August
    | September
    | October
    | November
    | Dezember

  days : (leapYear : Bool) -> Nat
  days leapYear = if leapYear then 366 else 365

  data Day : (leapYear : Bool) -> Type where
    MkDay : Fin (days leapYear) -> Day leapYear

namespace Month

  public export
  days : (leapYear : Bool) -> (month : Year.Month) -> Nat
  days leapYear month = case month of
    January => 31
    February => if leapYear then 29 else 28
    March => 31
    April => 30
    May => 31
    June => 30
    July => 31
    August => 31
    September => 30
    October => 31
    November => 30
    Dezember => 31

  public export
  record Day (leapYear : Bool) (month : Year.Month) where
    constructor MkDay
    getDay : Fin (days leapYear month)

namespace Week

  public export
  data Day
    = Monday
    | Tuesday
    | Wednesday
    | Thursday
    | Friday
    | Saturday
    | Sunday

namespace Day

  public export
  record Hour where
    constructor MkHour
    getHour : Fin 24

namespace Hour

  public export
  record Minute where
    constructor MkMinute
    getMinute : Fin 60

namespace Minute

  public export
  record Second where
    constructor MkSecond
    getSecond : Fin 60
