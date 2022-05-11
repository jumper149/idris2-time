module Data.Time

import Data.Fin

namespace Year

  public export
  data Month : Type where
    January : Month
    February : Month
    March : Month
    April : Month
    May : Month
    June : Month
    July : Month
    August : Month
    September : Month
    October : Month
    November : Month
    Dezember : Month

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
  data Day : (leapYear : Bool) -> (month : Year.Month) -> Type where
    MkDay : Fin (days leapYear month) -> Day leapYear month

namespace Week

  public export
  data Day : Type where
    Monday : Day
    Tuesday : Day
    Wednesday : Day
    Thursday : Day
    Friday : Day
    Saturday : Day
    Sunday : Day

namespace Day

  public export
  data Hour : Type where
    MkHour : Fin 24 -> Hour

namespace Hour

  public export
  data Minute : Type where
    MkMinute : Fin 60 -> Minute

namespace Minute

  public export
  data Second : Type where
    MkSecond : Fin 60 -> Second
