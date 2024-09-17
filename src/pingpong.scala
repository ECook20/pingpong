import scala.io.Source
import scala.io.StdIn
import java.io.PrintWriter
import java.io.File
import scala.collection.mutable.LinkedHashMap

enum Kappa:
    case Ucol
    case Col
    case Ocol

enum Agg:
    case Max
    case Min
    case Mean
    case Count
    // add some cool aggregators (e.g. var, std)

enum Criterion:
    case Crit(label: String, tm: Term, comp: Comparison)
    case CNot(c1: Criterion)
    case CAnd(c1: Criterion, c2: Criterion)
    case COr(c1: Criterion, c2: Criterion)

enum Comparison:
    case GT
    case LT
    case EQ

enum Relational:
    case Union  
    case Intersection 
    case Difference
    case Join

enum Token:
    case TAssign
    case KW_read
    case KW_write

    case TLParen
    case TRParen
    case TLBrack
    case TRBrack
    case TLCurly
    case TRCurly
    case TArrow
    case TComma
    case KW_bool(b: Boolean)
    case KW_int(i: Int)
    case KW_string(s: String)
    case KW_float(f: Float)
    case TVar(varName:String) // one or more lowercase letters
    case KW_some
    case KW_none

    case KW_col(k: Kappa)

    case KW_colindex
    case KW_rec
    case KW_recselect

    case KW_df
    case KW_dfselect
    case KW_dfinsert

    case KW_agg
    
    case KW_proj
    case KW_union
    case KW_intersect
    case KW_diff

    case KW_cross
    case KW_join
    case KW_where
    case KW_unqwhere

    case KW_groupby

    case KW_cand
    case KW_cor 
    case KW_cnot

    case KW_unwrap

    case TTy(tau: Type)
    case TTyCol(kappa: Kappa)
    case TTyRec
    case TTyDF
    case TTyOpt

    case TCriterion
    case TComp(c: Comparison)
    case TAgg(agg: Agg)

enum Type:
    case TyBool
    case TyInt
    case TyFloat
    case TyString

    case TyOpt(tau1:Type)

    case TyCol(tau1:Type, k:Kappa)
    case TyRec(rd:LinkedHashMap[String, Type])
    case TyDF(cols:LinkedHashMap[String, Type])

enum Term:
    case TmBool(b:Boolean)
    case TmInt(n:Int)
    case TmFloat(f:Float)
    case TmString(s:String)

    case TmVar(varName:String)

    case TmSome(t1:Term)
    case TmNone(tau:Type)

    case TmCol(col:Array[Term], k:Kappa)
    case TmColIndex(col:Term, ind:Term)
    case TmRec(rd:LinkedHashMap[String,Term])
    case TmRecSelect(rd:Term,key:String)

    case TmDF(df:LinkedHashMap[String, Term])
    case TmDFSelect(df:Term, key:String)
    case TmDFInsert(df:Term, label:String, col:Term)

    case TmAgg(agg:Agg,t1:Term)
    
    case TmProj(t1:Term, labels:Array[String])
    case TmUnion(t1:Term, t2:Term)
    case TmIntersection(t1:Term, t2:Term)
    case TmDiff(t1:Term, t2:Term)

    case TmCross(t1:Term, t2:Term)
    case TmJoin(t1:Term, t2:Term, on:Array[String])
    case TmWhere(t1:Term, c1:Criterion)
    case TmUnqWhere(t1:Term, c1:Criterion)
    case TmGroupBy(t1:Term, labels:Array[(Option[Agg], String)], gb:Array[String])

    // combinatoric n-pairs as derived form (where + cross?)

    case TmRead(fn:Term, etau:Type)
    case TmWrite(t1:Term, fn:Term)
    case TmUnwrap(t1:Term)

import Kappa.*
import Agg.*

import Criterion.*
import Comparison.*
import Relational.*
import Token.*
import Type.*
import Term.*

// entryToTerm: converts a csv entry to the corresponding term as a member of TyCol(tau, kappa)
    // Input: 
    //  entry: the csv entry  // tau, kappa: the parameters of TyCol(tau, kappa)
    // Output: the corresponding Term

def entryToTerm(entry: String, tau: Type, kappa: Kappa) : Term = {
    (entry, tau, kappa) match {
        case ("NULL", tau, Ocol) => TmNone(tau)
        case ("NULL", tau, kappa) => throw new Exception("NULL encountered in non-optional column")
        case (entry, TyString, Ocol) => TmSome(TmString(entry))
        case (entry, TyInt, Ocol) => TmSome(TmInt(entry.toInt))
        case (entry, TyFloat, Ocol) => TmSome(TmFloat(entry.toFloat))
        case ("true", TyBool, Ocol) => TmSome(TmBool(true))
        case ("false", TyBool, Ocol) => TmSome(TmBool(false))
        case (entry, TyString, _) => TmString(entry)
        case (entry, TyInt, _) => TmInt(entry.toInt)
        case (entry, TyFloat, _) => TmFloat(entry.toFloat)
        case ("true", TyBool, _) => TmBool(true)
        case ("false", TyBool, _) => TmBool(false)

        case _ => throw new Exception("Attmpted to parse incorrect column type")
    }
}

// helper for checkColumn, assigns code for recommendations
def kappaCode(kappa: Kappa) : Int = { kappa match
    case Ucol => 3
    case Col => 2
    case Ocol => 1
}

// helper for recommmendations, reformats kappa to string equivalent
def kappaToString(kappa: Kappa) : String = { kappa match
    case Ucol => "ucol"
    case Col => "col"
    case Ocol => "ocol"
}

// checkColumn: checks a column read in from csv for kappa-related errors/recommendations
// Input: 
//   ctau: the type of the column (as stored in the constructed DF) 
//   col: the column term -- potentially incorrect kappa
// Output: returns a recommended Kappa if possible, otherwise None
//   also throws an error for incorrect columns
def checkColumn(ctau: Type, col: Term) : Option[Kappa] = {
    var bestKappa: Kappa = Ocol
    (ctau, col) match {
        case (TyCol(tau, kappa), TmCol(arr, _)) =>
            val entrySet = arr.toSet

            if (!(entrySet.contains(TmNone(tau)))) {
                bestKappa = Col
                if (entrySet.size == arr.length) {
                    bestKappa = Ucol
                }
            }

            if (kappaCode(bestKappa) < kappaCode(kappa)) {
                throw new Exception(kappaToString(kappa) + " expected, but " + kappaToString(bestKappa) + " given")
            }
            if (kappaCode(bestKappa) > kappaCode(kappa)) {
                return Some(bestKappa)
            }
            return None

        case (_, _) => throw new Exception("improper call to checkColumn -- must pass column type + term")
    }
}

def read_csv(fileName: String, dftype: Type) : Term = {

    val lines = scala.io.Source.fromFile(fileName).getLines()

    dftype match {
        case TyDF(cols) => 
            var df_term_cols = LinkedHashMap[String, Term]()
            var labels = Array("")

            for ((line, lnum) <- lines.zipWithIndex) {

                if (lnum == 0) {
                    // verifies that label present in csv <-> col present in declared dataframe type
                    labels = line.split(",")
                    for (label <- labels) {
                        if (!(cols.contains(label))) { throw new Exception("col present in csv, not in declared dataframe type")}
                    }
                    for (key <- cols.keys) {
                        if (!(labels.contains(key))) { throw new Exception("col present in declared dataframe type, not in csv")}
                    }
                    // initialize contents of df term (empty column arrays)
                    for (label <- labels) {
                        df_term_cols = df_term_cols.++(Map(label -> TmCol(Array[Term](), Col)))
                    }

                } else {
                    val entries = line.split(",")
                    for (i <- 0 to entries.length - 1) {
                        (cols(labels(i)), df_term_cols(labels(i))) match {
                            case (TyCol(tau, kappa), TmCol(arr, k)) => 
                                try {
                                    df_term_cols += (labels(i) -> TmCol(arr :+ entryToTerm(entries(i), tau, kappa), k))
                                } catch { 
                                    case e => throw new Exception("Error in csv reader: " + e) 
                                }
                            case _ => throw new Exception("Error in csv reader")
                                
                        }
                    }
                }
            }

            // moving to recommendations
            var recomms = Map[String, Kappa]()
            for (label <- labels) {
                try {
                    checkColumn(cols(label), df_term_cols(label)) match {
                    case Some(kappa) => recomms += (label -> kappa)
                    case None => // pass
                    }

                } catch {
                    case e => throw new Exception("Error encountered on column '" + label + "': " + e)
                }
            }

            for (label <- recomms.keys) {
                cols(label) match {
                    case TyCol(tau, oldKappa) => {
                        println("Recommendation found! Column \"" + label + "\" is typed as " + kappaToString(oldKappa) +
                        ", but could be upgraded to " + kappaToString(recomms(label)))

                        var need_input = true
                        while (need_input) {
                            var input = scala.io.StdIn.readLine("Continue execution? [y/n]> ")
                            input.toList match {
                                case 'y'::tl => need_input = false
                                case 'n'::tl => throw new Exception("Ending execution (user request)")
                                case List() => need_input = false
                                case _ => // pass
                            }
                        }
                    
                    }
                    case _ => throw new Exception("csv reader -- null error")
                }
            }
            return TmDF(df_term_cols)

        case _ => throw new Exception("dftype input is malformed")
    }
}

def entry_to_string(tm: Term) : String = tm match {
    case TmInt(i) => i.toString
    case TmFloat(i) => i.toString
    case TmString(i) => i
    case TmBool(i) => i.toString
    case TmSome(TmInt(i)) => i.toString
    case TmSome(TmFloat(i)) => i.toString
    case TmSome(TmString(i)) => i
    case TmSome(TmBool(i)) => i.toString
    case TmNone(_) => "NULL"
    case _ => throw new Exception("non-base-term input to csv writer")
}

def df_to_string(df: Term) : String = df match {
    case TmDF(cols) => 
        var ret = cols.keys.mkString(",") + "\n"
        val length = cols.valuesIterator.next() match {
            case TmCol(arr, _) => arr.length
            case _ => throw new Exception("write -- null error")
        }

        for (i <- 0 to length - 1) {
            var row_str : Array[String] = Array()
            for (col <- cols.values) {
                col match {
                    case TmCol(arr, _) => 
                        row_str :+= entry_to_string(arr(i))
                    case _ => throw new Exception("write -- null error")
                }
            }
            ret += row_str.mkString(",") + "\n"
        }
        return ret
        
    case _ => throw new Exception("write -- non-df input")
}

def write_csv(df: Term, fileName: String) = {
    val writer = new PrintWriter(new File(fileName))
    writer.write(df_to_string(df))
    writer.close
}



def concat1(c:Char,pr:(String,List[Char])) = pr match {
  case (s,cs) => (s"${c}$s",cs)
}

def gatherChars(test:Char=>Boolean,cs:List[Char]): (String,List[Char]) = cs match {
  case Nil => ("",Nil)
  case c::tl if test(c) => concat1(c,gatherChars(test,tl))
  case _ => ("",cs)
}

def nextToken(cs:List[Char]): Option[(Token,List[Char])] = cs match {
  case Nil => None
  case '('::tl => Some(TLParen,tl)
  case ')'::tl => Some(TRParen,tl)
  case '['::tl => Some(TLBrack,tl) // list of column labels -- strings
  case ']'::tl => Some(TRBrack,tl)
  case '{'::tl => Some(TLCurly,tl) // list of column labels -- strings
  case '}'::tl => Some(TRCurly,tl)
  case ','::tl => Some(TComma,tl)
  case '-'::'>'::tl => Some(TArrow,tl)

  case '>'::tl => Some(TComp(GT),tl)
  case '='::'='::tl => Some(TComp(EQ),tl)
  case '<'::tl => Some(TComp(LT),tl)
  case '='::tl => Some(TAssign,tl)

  case c::tl if c.isLower => gatherChars(_.isLetterOrDigit,cs) match {
    case ("col",tll) => Some(KW_col(Col),tll)
    case ("ocol",tll) => Some(KW_col(Ocol),tll)
    case ("ucol",tll) => Some(KW_col(Ucol),tll)
    case ("colindex",tll) => Some(KW_colindex,tll)
    case ("rec",tll) => Some(KW_rec,tll)
    case ("recselect",tll) => Some(KW_recselect,tll)
    case ("df",tll) => Some(KW_df, tll)
    case ("dfselect",tll) => Some(KW_dfselect,tll)
    case ("dfinsert",tll) => Some(KW_dfinsert,tll)
    case ("agg",tll) => Some(KW_agg,tll)
    case ("proj",tll) => Some(KW_proj,tll)
    case ("union",tll) => Some(KW_union,tll)
    case ("intersect",tll) => Some(KW_intersect,tll)
    case ("diff",tll) => Some(KW_diff,tll)
    case ("cross",tll) => Some(KW_cross,tll)
    case ("join",tll) => Some(KW_join,tll)
    case ("where",tll) => Some(KW_where,tll)
    case ("unqwhere",tll) => Some(KW_unqwhere,tll)
    case ("groupby",tll) => Some(KW_groupby,tll)

    case ("true",tll) => Some(KW_bool(true),tll)
    case ("false",tll) => Some(KW_bool(false),tll)
    case ("not",tll) => Some(KW_cnot,tll)
    case ("and",tll) => Some(KW_cand,tll)
    case ("or",tll) => Some(KW_cor,tll)
    case ("some",tll) => Some(KW_some, tll)
    case ("none",tll) => Some(KW_none, tll)

    case ("read",tll) => Some(KW_read, tll)
    case ("write",tll) => Some(KW_write, tll)
    case ("unwrap",tll) => Some(KW_unwrap,tll)

    case (x, tll) => Some(TVar(x),tll)
    
  }

  case '"'::tl => gatherChars(c => c != '"', tl) match {
    case (s, tll) => tll match
      case c::tll => Some(KW_string(s),tll)
      case _ => throw new Exception("scan error: unexpected eof in string scan")
  }

  case '-'::tl => gatherChars(_.isDigit,tl) match {
    case (i1, tll) => tll match
      case '.'::tll => gatherChars(_.isDigit,tll) match
        case (i2, tll) => try {
            return Some(KW_float((i1 + "." + i2).toFloat * -1), tll)
          } catch { case _ => throw new Exception("scan error: error in parsing float literal") }
      case tll => try {
          return Some(KW_int(i1.toInt * -1), tll)
        } catch { case _ => throw new Exception("scan error: error in parsing int literal") }
  }

  case c::tl if c.isDigit => gatherChars(_.isDigit,cs) match {
    case (i1, tll) => tll match
      case '.'::tll => gatherChars(_.isDigit,tll) match
        case (i2, tll) => try {
            return Some(KW_float((i1 + "." + i2).toFloat), tll)
          } catch { case _ => throw new Exception("scan error: error in parsing float literal") }
      case tll => try {
          return Some(KW_int(i1.toInt), tll)
        } catch { case _ => throw new Exception("scan error: error in parsing int literal") }
  }

  case c::tl if c.isUpper => gatherChars(_.isUpper,cs) match {
    case ("I",tll) => Some(TTy(TyInt),tll)
    case ("F",tll) => Some(TTy(TyFloat),tll)
    case ("B",tll) => Some(TTy(TyBool),tll)
    case ("S",tll) => Some(TTy(TyString),tll)
    case ("X",tll) => Some(TCriterion,tll)

    case (_, tll) => gatherChars(_.isLetter,cs) match {
      case ("Col",tll) => Some(TTyCol(Col), tll)
      case ("Ucol",tll) => Some(TTyCol(Ucol), tll)
      case ("Ocol",tll) => Some(TTyCol(Ocol), tll)
      case ("Rec",tll) => Some(TTyRec, tll)
      case ("DF",tll) => Some(TTyDF, tll)
      case ("Opt",tll) => Some(TTyOpt, tll)

      case ("Max",tll) => Some(TAgg(Max),tll)
      case ("Min",tll) => Some(TAgg(Min),tll)
      case ("Mean",tll) => Some(TAgg(Mean),tll)
      case ("Count",tll) => Some(TAgg(Count),tll)
      case _ => throw new Exception("scan error: variables must begin with lowercase letters")
    }
  }


  case c::tl if c.isWhitespace => nextToken(tl)
  case c::_ => throw new Exception(s"scan error: $c")
}

def scan(code:String): List[Token] =
  def lp(cs:List[Char]): List[Token] = nextToken(cs) match {
    case None => Nil
    case Some(tok,cs) => tok::lp(cs)
  }
  return lp(code.toList)

// ===== parser

def unparse_crit(c: Criterion): String = c match { 
  case Crit(label, tm, comp) => comp match
    case GT => return label + " > " + unparse(tm)
    case EQ => return label + " == " + unparse(tm)
    case LT => return label + " < " + unparse(tm)
  case CNot(c1) => return "not(" + unparse_crit(c1) + ")"
  case CAnd(c1, c2) => return "and(" + unparse_crit(c1) + ", " + unparse_crit(c2) + ")"
  case COr(c1, c2) => return "or(" + unparse_crit(c1) + ", " + unparse_crit(c2) + ")"

}

def agg_to_string(agg: (Option[Agg], String)): String = agg match {
    case (Some(Max), s) => "max_" + s
    case (Some(Min), s) => "min_" + s
    case (Some(Mean), s) => "mean_" + s
    case (Some(Count), s) => "count_" + s
    case (None, s) => s
}

def unparse(tm: Term): String = tm match {
  case TmBool(b) => b.toString
  case TmInt(n) => n.toString
  case TmFloat(f) => f.toString
  case TmString(s) => "\"" + s + "\""
  case TmVar(varName) => varName
  case TmSome(t1) => "Some(" + unparse(t1) + ")"
  case TmNone(_) => "None"

  case TmUnwrap(t1) => "Unwrap(" + unparse(t1) + ")"

  case TmRead(fn, _) => "Read(" + unparse(fn) + ")"
  case TmWrite(t1, fn) => "Read(" + unparse(t1) + ", " + unparse(fn) + ")"

  case TmCol(col, _) => 
    var column = "["
    col.foreach{ tm1 => column += unparse(tm1) + ", " }
    if (column.length == 1) { return "[]" } else { return column.substring(0,column.length - 2) + "]"}

  case TmColIndex(col, ind) => "ColumnIndex(" + unparse(col) + ", " + unparse(ind) + ")"
  case TmRec(rd) => 
    var record = "{"
    rd.keys.foreach{ key => record += key + " -> " + unparse(rd(key)) + ", " }
    if (record.length == 1) { return "{}" } else { return record.substring(0,record.length - 2) + "}"}

  case TmRecSelect(rd,key) => "RecordSelect(" + unparse(rd) + ", " + key + ")"

  case TmDF(df) => 
    var df1 = "{[\n"
    df.keys.foreach{ key => df1 += "   " + key + " -> " + unparse(df(key)) + ", \n"}
    if (df1.length == 3) { return "{[ ]}" } else { return df1.substring(0,df1.length - 3) + "\n]}" }
  case TmDFSelect(df, key) => "DFSelect(" + unparse(df) + ", " + key + ")"
  case TmDFInsert(df, label, col) => "DFInsert(" + unparse(df) + ", " + label + ", " + unparse(col) + ")" 

  case TmAgg(agg,t1) => agg match
    case Max => return "Agg(Max, " + unparse(t1) + ")"
    case Min => return "Agg(Min, " + unparse(t1) + ")"
    case Mean => return "Agg(Mean, " + unparse(t1) + ")"
    case Count => return "Agg(Count, " + unparse(t1) + ")"
  
  case TmProj(t1, labels) => "Proj(" + unparse(t1) + ", [" + labels.mkString(", ") + "])"
  case TmUnion(t1, t2) => "Union(" + unparse(t1) + ", " + unparse(t2) + ")"
  case TmIntersection(t1, t2) => "Intersect(" + unparse(t1) + ", " + unparse(t2) + ")"
  case TmDiff(t1, t2) => "Diff(" + unparse(t1) + ", " + unparse(t2) + ")"

  case TmCross(t1, t2) => "Cross(" + unparse(t1) + ", " + unparse(t2) + ")"
  case TmJoin(t1, t2, on) => "Join(" + unparse(t1) + ", " + unparse(t2) + ", [" + on.mkString(", ") + "])"
  case TmWhere(t1, c1) => "Where(" + unparse(t1) + ", " + unparse_crit(c1) + ")"
  case TmUnqWhere(t1, c1) => "UnqWhere(" + unparse(t1) + ", " + unparse_crit(c1) + ")"

  case TmGroupBy(t1, labels, gb) => "GroupBy(" + unparse(t1) + ", [" + labels.mkString(", ") + "], [" + gb.mkString(",") + "])"

}


def nextTy(toks:List[Token]): Option[(Type,List[Token])] = toks match {
  case Nil => None
  case TTy(tau) :: tl => Some(tau, tl)
  case TTyOpt :: TLBrack :: tl => nextTy(tl) match
    case Some(tau, TRBrack :: tl) => Some(TyOpt(tau), tl)
    case _ => throw new Exception("type parse error: TyOpt")
  case TTyCol(kappa) :: TLBrack :: tl => nextTy(tl) match
    case Some(tau, TRBrack :: tl) => Some(TyCol(tau, kappa), tl)
    case _ => throw new Exception("type parse error: TyCol")

  case TTyRec :: TLBrack :: TLCurly :: tl => 
    var map : LinkedHashMap[String, Type] = LinkedHashMap()
    var tll = tl

    while (true) {
      tll match
        case KW_string(l) :: TArrow :: tl => nextTy(tl) match
          case Some(tau, tl) => tl match
            case TComma :: tl => 
              map = map.++(Map(l -> tau))
              tll = tl
            case TRCurly :: TRBrack :: tl => return Some(TyRec(map.++(Map(l -> tau))), tl) 
            case _ => throw new Exception("parse error: unexpected end to rec type literal")
            
          case None => throw new Exception("parse error: unexpected eof in rec type literal ")
        case _ => throw new Exception("parse error: unexpected end to rec type ")
    }
    throw new Exception("parse error in rec -- null error")

  case TTyDF :: TLBrack :: TLCurly :: tl => 
    var map : LinkedHashMap[String, Type] = LinkedHashMap()
    var tll = tl

    while (true) {
      tll match
        case KW_string(l) :: TArrow :: tl => nextTy(tl) match
          case Some(tau, tl) => tl match
            case TComma :: tl => 
              map = map.++(Map(l -> tau))
              tll = tl
            case TRCurly :: TRBrack :: tl => return Some(TyDF(map.++(Map(l -> tau))), tl) 
            case _ => throw new Exception("parse error: unexpected end to df type literal")
            
          case None => throw new Exception("parse error: unexpected eof in df type literal ")
        case _ => throw new Exception("parse error: unexpected end to df type ")
    }
    throw new Exception("parse error in df type -- null error")

  case _ => throw new Exception("type parse error: received type-unrelated tokens")
}



def nextTerm(toks:List[Token]): Option[(Term,List[Token])] = toks match {
  case Nil => None

  case KW_read::TLParen::tl => nextTerm(tl) match
    case Some(tm, TComma::tl) => nextTy(tl) match
      case Some(tau, TRParen::tl) => Some(TmRead(tm, tau), tl)
      case _ => throw new Exception("parse error: read")
    case _ => throw new Exception("parse error: read")

  case KW_write::TLParen::tl => nextTerm(tl) match
    case Some(tm, TComma::tl) => nextTerm(tl) match
      case Some(tm1, TRParen::tl) => Some(TmWrite(tm, tm1), tl)
      case _ => throw new Exception("parse error: read")
    case _ => throw new Exception("parse error: read")

  case KW_unwrap::TLParen::tl => nextTerm(tl) match
    case Some(tm, TRParen::tl) => return Some(TmUnwrap(tm),tl)
    case _ => throw new Exception("parse error: unwrap")

  case TVar(x)::tl => Some(TmVar(x),tl)
  case KW_bool(b)::tl => Some(TmBool(b),tl)
  case KW_int(i)::tl => Some(TmInt(i),tl)
  case KW_string(s)::tl => Some(TmString(s),tl)
  case KW_float(f)::tl => Some(TmFloat(f),tl)
  case KW_some::TLParen::tl => nextTerm(tl) match  
    case Some(tm, TRParen :: tl1) => return Some(TmSome(tm), tl1)
    case _ => throw new Exception("parse error: some")
  case KW_none :: TLParen :: tl => nextTy(tl) match
    case Some(tau, TRParen :: tl1) => return Some(TmNone(tau), tl1)
    case _ => throw new Exception("parse error: none")

  case KW_col(kappa)::TLParen::TLBrack::tl =>
    var col : Array[Term] = Array()
    var tll = tl

    while (true) {
      nextTerm(tll) match
        case Some(tm, tl) => tl match
          case TComma :: tl => 
            col = col :+ tm
            tll = tl
          case TRBrack :: TRParen :: tl => return Some(TmCol(col :+ tm, kappa), tl)
          case _ => throw new Exception("parse error: unexpected end to col literal")
        case None => throw new Exception("parser error: unexpected eof in col")
    }
    throw new Exception("parse error in col -- null error")

  case KW_rec::TLParen::TLCurly::tl =>
    var map : LinkedHashMap[String, Term] = LinkedHashMap()
    var tll = tl

    while (true) {
      tll match
        case KW_string(l) :: TArrow :: tl => nextTerm(tl) match
          case Some(tm, tl) => tl match
            case TComma :: tl => 
              map = map.++(Map(l -> tm))
              tll = tl
            case TRCurly :: TRParen :: tl => return Some(TmRec(map.++(Map(l -> tm))), tl) 
            case _ => throw new Exception("parse error: unexpected end to rec literal")
            
          case None => throw new Exception("parse error: unexpected eof in rec literal")
        case _ => throw new Exception("parse error: unexpected end to rec literal")
    }
    throw new Exception("parse error in rec -- null error")

  case KW_df::TLParen::TLCurly::tl => 
    var df : LinkedHashMap[String, Term] = LinkedHashMap()
    var tll = tl

    while (true) {
      tll match
        case KW_string(l) :: TArrow :: tl => nextTerm(tl) match
          case Some(tm, tl) => tl match
            case TComma :: tl => 
              df = df.++(Map(l -> tm))
              tll = tl
            case TRCurly :: TRParen :: tl => return Some(TmDF(df.++(Map(l -> tm))), tl) 
            case _ => throw new Exception("parse error: unexpected end to df literal")
            
          case None => throw new Exception("parse error: unexpected eof in df literal")
        case _ => throw new Exception("parse error: unexpected end to df literal")
    }
    throw new Exception("parse error in rec -- null error")

  case KW_colindex::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma :: tl) => nextTerm(tl) match
      case Some(tm2, TRParen :: tl) => Some(TmColIndex(tm1, tm2), tl)
      case _ => throw new Exception("parse error: column index")
    case _ => throw new Exception("parse error: column index")
  case KW_recselect::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma :: tl) => tl match
      case KW_string(l) :: TRParen :: tl => Some(TmRecSelect(tm1, l), tl)
      case _ => throw new Exception("parse error: record selection")
    case _ => throw new Exception("parse error: record selection")
  case KW_dfselect::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma :: tl) => tl match
      case KW_string(l) :: TRParen :: tl => Some(TmDFSelect(tm1, l), tl)
      case _ => throw new Exception("parse error: df selection")
    case _ => throw new Exception("parse error: df selection")
  case KW_dfinsert::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma :: tl) => tl match
      case KW_string(l) :: TComma :: tl => nextTerm(tl) match
        case Some(tm2, TRParen :: tl) => Some(TmDFInsert(tm1, l, tm2), tl)
        case _ => throw new Exception("parse error: df insert")
      case _ => throw new Exception("parse error: df insert")
    case _ => throw new Exception("parse error: df insert")

  case KW_agg::TLParen::TAgg(agg)::TComma::tl => nextTerm(tl) match
    case Some(tm1, TRParen :: tl) => Some(TmAgg(agg, tm1), tl)
    case _ => throw new Exception("parse error: aggregation")

  case KW_proj::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma :: TLBrack :: tl) => 
      var labels : Array[String] = Array()
      var tll = tl

      while (true) {
        tll match
          case KW_string(l) :: TComma :: tl => 
            labels = labels :+ l
            tll = tl
          case KW_string(l) :: TRBrack :: TRParen :: tl => return Some(TmProj(tm1, labels :+ l), tl)
          case _ => throw new Exception("parse error: unexpected end to label array (df proj)")
        }
        
        throw new Exception("parse error in df proj - null error")
    case _ => throw new Exception("parse error: df proj")

  case KW_union::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma::tl) => nextTerm(tl) match
      case Some(tm2, TRParen::tl) => Some(TmUnion(tm1, tm2), tl)
      case _ => throw new Exception("parse error: df union")
    case _ => throw new Exception("parse error: df union")
  case KW_intersect::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma::tl) => nextTerm(tl) match
      case Some(tm2, TRParen::tl) => Some(TmIntersection(tm1, tm2), tl)
      case _ => throw new Exception("parse error: df intersection")
    case _ => throw new Exception("parse error: df intersection")
  case KW_diff::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma::tl) => nextTerm(tl) match
      case Some(tm2, TRParen::tl) => Some(TmDiff(tm1, tm2), tl)
      case _ => throw new Exception("parse error: df difference")
    case _ => throw new Exception("parse error: df difference")

  case KW_cross::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma::tl) => nextTerm(tl) match
      case Some(tm2, TRParen::tl) => Some(TmCross(tm1, tm2), tl)
      case _ => throw new Exception("parse error: df cross")
    case _ => throw new Exception("parse error: df cross")

  case KW_join::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma::tl) => nextTerm(tl) match
      case Some(tm2, TComma::TLBrack::tl) => 
        var labels : Array[String] = Array()
        var tll = tl

        while (true) {
          tll match
            case KW_string(l) :: TComma :: tl => 
              labels = labels :+ l
              tll = tl

            case KW_string(l) :: TRBrack :: TRParen :: tl => return Some(TmJoin(tm1, tm2, labels :+ l), tl)
            case _ => throw new Exception("parse error: unexpected end to label array (df join)")
        }
        throw new Exception("error in df join parse -- null error")

      case _ => throw new Exception("parse error: df join")
    case _ => throw new Exception("parse error: df join")

  case KW_where::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma::TCriterion::TLParen::tl) => nextCrit(tl) match
      case Some(c1, TRParen::TRParen::tl) => Some(TmWhere(tm1, c1), tl)
      case _ => throw new Exception("parse error: df select")
    case _ => throw new Exception("parse error: df select")

  case KW_unqwhere::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma::TCriterion::TLParen::tl) => nextCrit(tl) match
      case Some(c1, TRParen::TRParen::tl) => Some(TmUnqWhere(tm1, c1), tl)
      case _ => throw new Exception("parse error: df unique select")
    case _ => throw new Exception("parse error: df unique select")

  case KW_groupby::TLParen::tl => nextTerm(tl) match
    case Some(tm1, TComma :: TLBrack :: tl) => 
      var labels : Array[(Option[Agg], String)] = Array()
      var tll = tl
      var continue = true

      while (continue) {
        tll match
          case TAgg(agg)::TLParen:: KW_string(l)::TRParen::TComma :: tl => 
            labels = labels :+ (Some(agg), l)
            tll = tl
          case KW_string(l) :: TComma :: tl => 
            labels = labels :+ (None, l)
            tll = tl
          case TAgg(agg)::TLParen::KW_string(l)::TRParen::TRBrack::TComma::TLBrack::tl => 
            labels = labels :+ (Some(agg), l)
            tll = tl
            continue = false
          case KW_string(l) :: TRBrack :: TComma :: TLBrack :: tl => 
            labels = labels :+ (None, l)
            tll = tl
            continue = false

          case _ => throw new Exception("parse error: unexpected end to label array (df groupby)")
        }

      var gb : Array[String] = Array()
      while (true) {
        tll match
          case KW_string(l) :: TComma :: tl => 
            gb = gb :+ l
            tll = tl
          case KW_string(l) :: TRBrack :: TRParen :: tl => return Some(TmGroupBy(tm1, labels, gb :+ l), tl)
          case _ => throw new Exception("parse error: unexpected end to gb array (df groupby)")
        }
        
        throw new Exception("parse error in df proj - null error")
    case _ => throw new Exception("parse error: df proj")


  case c::_ => throw new Exception(s"unexpected parse token: $c")

}

def nextCrit(toks:List[Token]): Option[(Criterion,List[Token])] = toks match {
  case KW_string(l) :: TComp(comp) :: tl => nextTerm(tl) match
    case Some(tm, tl) => Some(Crit(l, tm, comp), tl)
    case _ => throw new Exception("parse error: unexpected eof in criterion")
  case KW_cnot :: TLParen :: tl => nextCrit(tl) match
    case Some(c1, TRParen::tl) => Some(CNot(c1), tl)
    case _ => throw new Exception("parse error: cnot")
  case KW_cand :: TLParen :: tl => nextCrit(tl) match
    case Some(c1, TComma :: tl) => nextCrit(tl) match
      case Some(c2, TRParen :: tl) => Some(CAnd(c1, c2), tl)
      case _ => throw new Exception("parse error: cand")
    case _ => throw new Exception("parse error: cand")
  case KW_cor :: TLParen :: tl => nextCrit(tl) match
    case Some(c1, TComma :: tl) => nextCrit(tl) match
      case Some(c2, TRParen :: tl) => Some(COr(c1, c2), tl)
      case _ => throw new Exception("parse error: cor")
    case _ => throw new Exception("parse error: cor")

  case c :: _ => throw new Exception(s"parse error: token $c cannot be processed in criterion")
  case _ => throw new Exception("parse error: criterion")
}

def parse(toks: List[Token]): Term = nextTerm(toks) match {
  case None => throw new Exception("parse error: not enough program")
  case Some(st,Nil) => st
  case Some(_,_) => throw new Exception("parse error: too much program")
}

// ===== type environments

type TypeEnv = Map[String, Type]
val emptyTypeEnv: TypeEnv = Map()

def lookup(x: String, gamma: TypeEnv): Option[Type] = if gamma.contains(x) then return Some(gamma(x)) else return None
def extend(x: String, tau: Type, gamma: Map[String, Type]): TypeEnv = gamma + (x -> tau)

type AggTypeEnv = Map[(Agg, Type), Type]
val emptyAggEnv: AggTypeEnv = Map()

def lookup_agg(x: (Agg, Type), g_agg: AggTypeEnv): Option[Type] = if g_agg.contains(x) then return Some(g_agg(x)) else return None
def extend_agg(x: (Agg, Type), tau: Type, g_agg: AggTypeEnv): AggTypeEnv = g_agg + (x -> tau)


type TermEnv = Map[String, Term]
val emptyTermEnv: TermEnv = Map()

def tm_lookup(x: String, vars: TermEnv): Option[Term] = if vars.contains(x) then return Some(vars(x)) else return None
def tm_extend(x: String, tm: Term, vars: Map[String, Term]): TermEnv = vars + (x -> tm)


def combine(col1: Type, col2: Type, r: Relational): TyCol = (col1, col2) match
    case (TyCol(t1, k1), TyCol(t2, k2)) => 
        if (t1 == t2) { 
            r match
                case Union => (k1, k2) match
                    case (Ocol, _) => return TyCol(t1, Ocol)
                    case (_, Ocol) => return TyCol(t1, Ocol)
                    case (_, _) => return TyCol(t1, Col)
                case Intersection => (k1, k2) match
                    case (Ucol, _) => return TyCol(t1, Ucol)
                    case (_, Ucol) => return TyCol(t1, Ucol)
                    case (Col, _) => return TyCol(t1, Col)
                    case (_, Col) => return TyCol(t1, Col)
                    case (Ocol, Ocol) => return TyCol(t1, Ocol)
                case Difference => (k1, k2) match
                    case (Ucol, _) => return TyCol(t1, Ucol)
                    case (Col, _) => return TyCol(t1, Col)
                    case (Ocol, _) => return TyCol(t1, Ocol)
                case Join => (k1, k2) match
                    case (Ocol, Ocol) => return TyCol(t1, Ocol)
                    case (Ucol, Ucol) => return TyCol(t1, Ucol)
                    case (_, _) => return TyCol(t1, Col)

        } else { throw new Exception("ill-typed column combination: attempting to combine different col types " + t1.toString + " and " + t2.toString) }

    case (_, _) => throw new Exception("ill-typed coljoin: mistyped inputs")


// helper function for type-checking criterions -- tells me the constraints upon df imposed by criterion
// needs to traverse the recursive criterion tree to do this
// no correctness checking -- this is done in the type-checking for Where/UnqWhere
def criterionSupport(gamma : TypeEnv, g_agg : AggTypeEnv, crit: Criterion) : List[(String, Type)] = crit match {
    case Crit(label, tm, comp) => List((label, typeOf(gamma, g_agg, tm)))
    case CNot(crit1) => criterionSupport(gamma, g_agg, crit1)
    case CAnd(crit1, crit2) => criterionSupport(gamma, g_agg, crit1) ++ criterionSupport(gamma, g_agg, crit2)
    case COr(crit1, crit2) => criterionSupport(gamma, g_agg, crit1) ++ criterionSupport(gamma, g_agg, crit2)
}

def N(col : Type): TyCol = col match {
    case TyCol(tau, Ucol) => TyCol(tau, Col)
    case TyCol(tau, Col) => TyCol(tau, Col)
    case TyCol(tau, Ocol) => TyCol(tau, Ocol)
    case _ => throw new Exception("input to N operator must be of type TyCol")
}

def R(df1: Type): TyRec = df1 match
    case TyDF(cols1) => try {
        var rd: LinkedHashMap[String, Type] = LinkedHashMap()
        cols1.keys.foreach { key =>
                cols1(key) match
                    case TyCol(tau, Ocol) => rd = rd.++(Map(key -> TyOpt(tau)))
                    case TyCol(tau, _) => rd = rd.++(Map(key -> tau))
                    case _ => throw new Exception("non-typechecked DF - null error")
        }
        return TyRec(rd)

    } catch { case _ => throw new Exception("ill-typed R-op: missing col")}
    case _ => throw new Exception("ill-typed R-op: df input")


// ===== type checking

// type checker
def typeOf(gamma: TypeEnv, g_agg : AggTypeEnv, t: Term): Type = t match {
    // standard type checking
    case TmBool(_) => TyBool
    case TmInt(_) => TyInt
    case TmFloat(_) => TyFloat
    case TmString(_) => TyString

    // type checking with wrinkles
    case TmRead(t1, tau) => t1 match
        case TmString(_) => return tau
        case _ => throw new Exception("ill-typed read: non-filename input")
    case TmWrite(t1, t2) => (typeOf(gamma, g_agg, t1), t2) match
        case (TyDF(_), TmString(_)) => return TyBool
        case (TyDF(_), _) => throw new Exception("ill-typed write: non-filename input")
        case (_, TmString(_)) => throw new Exception("ill-typed write: non-df input")
        case _=> throw new Exception("ill-typed write: inputs")
    case TmUnwrap(t1) => typeOf(gamma, g_agg, t1) match
        case TyOpt(tau) => return tau
        case _ => throw new Exception("ill-typed unwrap: called on non-optional term")

    case TmVar(x) => lookup(x, gamma) match
        case Some(tau1) => return tau1
        case None => throw new Exception("unassigned variable referenced")
    
    case TmSome(tm1) => typeOf(gamma, g_agg, tm1) match
        case tau1 => return TyOpt(tau1)
    case TmNone(tau) => TyOpt(tau)

    // column typing
    case TmCol(arr, k) => 
        val unique_tau = arr.map(typeOf(gamma, g_agg, _)).distinct
        val unique_tm = arr.distinct

        if (unique_tau.length > 1) { 
            throw new Exception("ill-typed column: contains elements of different types")
        }

        k match {
            case Ocol => unique_tau(0) match 
                case TyOpt(tau1) => return TyCol(tau1, Ocol)
                case _ => throw new Exception("ill-typed ocol: contains non-optional elements")
            case Col => return TyCol(unique_tau(0), Col)
            case Ucol => 
                if (unique_tm.length == arr.length) {
                    return TyCol(unique_tau(0), Ucol)
                } else { throw new Exception("ill-typed ucol: contains non-unique elements")}
        }

    case TmColIndex(col, ind) => (typeOf(gamma, g_agg, col), typeOf(gamma, g_agg, ind)) match
        case (TyCol(tau, kappa), TyInt) => kappa match
            case Ocol => return TyOpt(tau)
            case _ => return tau

        case _ => throw new Exception("ill-typed column index: improperly typed inputs")
    
    case TmRec(rd) => 
        var tau_rd : LinkedHashMap[String, Type] = LinkedHashMap() 
        rd.keys.foreach{ key => typeOf(gamma, g_agg, rd(key)) match
            case tau => tau_rd = tau_rd.++(Map(key -> tau))
        }

        return TyRec(tau_rd)
    
    case TmRecSelect(rd, key) => typeOf(gamma, g_agg, rd) match
        case TyRec(rd1) => try { return rd1(key)
        } catch { case _ => throw new Exception("ill-typed record select: label \"" + key + "\" not in record")}

        case _ => throw new Exception("ill-typed record select: non-record input")


    case TmDF(cols) => 
        var rd: LinkedHashMap[String, Type] = LinkedHashMap()
        cols.keys.foreach{ col => typeOf(gamma, g_agg, cols(col)) match
            case TyCol(tau, k) => rd = rd.++(Map(col -> TyCol(tau, k)))
            case _ => throw new Exception("ill-typed df: non-column type in cols")
        }
        return TyDF(rd)
    
    case TmDFSelect(df1, key) => typeOf(gamma, g_agg, df1) match
        case TyDF(cols1) => try { return cols1(key)
        } catch { case _ => throw new Exception("ill-typed df select: column label \"" + key + "\" not present in df")}

        case _ => throw new Exception("ill-typed df select: non-df input")

    case TmDFInsert(df, label, col) => (typeOf(gamma, g_agg, df), typeOf(gamma, g_agg, col)) match
        case (TyDF(cols), TyCol(tau, kappa)) => TyDF(cols.++(Map(label -> TyCol(tau, kappa))))
        
        case _ => throw new Exception("ill-typed df insert: inputs not of proper type")


    case TmAgg(agg, t1) => typeOf(gamma, g_agg, t1) match
        case TyCol(tau, kappa) => lookup_agg((agg, TyCol(tau, kappa)), g_agg) match
            case (Some(tau)) => return tau
            case None => throw new Exception("ill-typed agg: aggregator " + agg.toString + " cannot be applied to column with type " + tau.toString)

        case _ => throw new Exception("ill-typed agg: non-column input")

    case TmProj(df1, labels) => typeOf(gamma, g_agg, df1) match 
        case TyDF(cols1) => try {
            var ndf: LinkedHashMap[String, Type] = LinkedHashMap()
            labels.foreach{ label =>
                ndf = ndf.++(Map(label -> cols1(label)))
            }

            return TyDF(ndf)
        } catch { case _ => throw new Exception("ill-typed projection: requests columns not present in df") }

        case _ => throw new Exception("ill-typed projection: requires df input")

    case TmUnion(df1, df2) => (typeOf(gamma, g_agg, df1), typeOf(gamma, g_agg, df2)) match
        case (TyDF(cols1), TyDF(cols2)) => 
            if (cols1 == cols2) {
                var ndf: LinkedHashMap[String, Type] = LinkedHashMap()
                cols1.keys.foreach{ label =>
                    ndf = ndf.++(Map(label -> combine(cols1(label), cols2(label), Union)))  
                }

                return TyDF(ndf)

            } else { throw new Exception("ill-typed DF union: input dataframes must have same columns (in same order)") }

        case _ => throw new Exception("ill-typed DF union: requires dataframe inputs")

    case TmIntersection(df1, df2) => (typeOf(gamma, g_agg, df1), typeOf(gamma, g_agg, df2)) match
        case (TyDF(cols1), TyDF(cols2)) => 
            if (cols1 == cols2) {
                var ndf: LinkedHashMap[String, Type] = LinkedHashMap()
                cols1.keys.foreach{ label =>
                    ndf = ndf.++(Map(label -> combine(cols1(label), cols2(label), Intersection)))
                }

                return TyDF(ndf)

            } else { throw new Exception("ill-typed DF intersect: input dataframes must have same columns (in same order)") }

        case _ => throw new Exception("ill-typed DF intersect: requires dataframe inputs")
    
    case TmDiff(df1, df2) => (typeOf(gamma, g_agg, df1), typeOf(gamma, g_agg, df2)) match
        case (TyDF(cols1), TyDF(cols2)) => 
            if (cols1 == cols2) {
                var ndf: LinkedHashMap[String, Type] = LinkedHashMap()
                cols1.keys.foreach{ label =>
                    ndf = ndf.++(Map(label -> combine(cols1(label), cols2(label), Difference)))    
                }

                return TyDF(ndf)

            } else { throw new Exception("ill-typed DF difference: input dataframes must have same columns (in same order)") }

        case _ => throw new Exception("ill-typed DF difference: requires dataframe inputs")



    case TmCross(df1, df2) => (typeOf(gamma, g_agg, df1), typeOf(gamma, g_agg, df2)) match
        case (TyDF(cols1), TyDF(cols2)) =>
            var ndf: LinkedHashMap[String, Type] = LinkedHashMap()

            cols1.keys.foreach{ label =>
                ndf = ndf.++(Map(label -> N(cols1(label))))
            }
            cols2.keys.foreach{ label =>
                if (cols1.contains(label)) {
                    ndf = ndf.++(Map(label + "_1" -> N(cols2(label))))
                } else {
                    ndf = ndf.++(Map(label -> N(cols2(label))))
                }
            }

            return TyDF(ndf)
            
        case _ => throw new Exception("ill-typed cross: df inputs")


    case TmJoin(df1, df2, on) => (typeOf(gamma, g_agg, df1), typeOf(gamma, g_agg, df2)) match
        case (TyDF(cols1), TyDF(cols2)) =>
            // can't check that on is Array[String]
            var ndf: LinkedHashMap[String, Type] = LinkedHashMap()

            if (!(on.forall(label => (cols1.contains(label) && cols2.contains(label))))) {
                throw new Exception("ill-typed join: joining columns contain labels not in input dfs")
            }

            cols1.keys.foreach{ label =>
                on.find(_ == label) match 
                    case Some(_) => ndf = ndf.++(Map(label -> combine(cols1(label), cols2(label), Join)))
                    case None => ndf = ndf.++(Map(label -> N(cols1(label))))
            }
            cols2.keys.foreach{ label =>
                on.find(_ == label) match 
                    case Some(_) => // do nothing
                    case None => 
                        if (cols1.contains(label)) {
                            ndf = ndf.++(Map(label + "_1" -> N(cols2(label))))
                        } else {
                            ndf = ndf.++(Map(label -> N(cols2(label))))
                        }
            }

            return TyDF(ndf)

        case _ => throw new Exception("ill-typed join: df inputs")
        
        

    case TmWhere(t1, c1) => (typeOf(gamma, g_agg, t1), c1) match
        case (TyDF(cols), Crit(key, tau, EQ)) => // if unqwhere case, throw a recommendation and proceed

            if (!(cols.contains(key))) {
                throw new Exception("ill-typed where: criterion contains column " + key + ", but " + key + " not in df")
            } else { cols(key) match
                case TyCol(ctau, kappa) =>
                    if (ctau != typeOf(gamma, g_agg, tau)) { 
                        throw new Exception("ill-typed where: criterion expects different type on column " + key + " than is present in df")
                    }
                    kappa match {
                        case Ucol => println("Recommendation found! where called on unique column " + key + " with base EQ criterion" + 
                        " -- using unqwhere is possible and returns singular records!")
                        case _ => // pass
                    }
                case _ => throw new Exception("malformed columns - null error")
            }
            return TyDF(cols)

        case (TyDF(cols), _) => criterionSupport(gamma, g_agg, c1).distinct match
            case pairs =>
                var crit_reqs : Map[String, Type] = Map()
                pairs.foreach{ (key, tau) => 
                    if (crit_reqs.contains(key)) {
                        throw new Exception("ill-typed where: criterion expects different types on label " + key)
                    } else {
                        crit_reqs = crit_reqs + (key -> tau)
                    }
                }

                crit_reqs.keys.foreach{ key => 
                    if (!(cols.contains(key))) {
                        throw new Exception("ill-typed where: criterion contains column " + key + ", but " + key + " not in df")
                    } else { cols(key) match
                        case TyCol(tau, _) => 
                            if (tau != crit_reqs(key)) {
                                throw new Exception("ill-typed where: criterion expects different type on column " + key + " than is present in df")
                            }
                        case _ => throw new Exception("malformed columns - null error")
                    }
                }
                
                return TyDF(cols)
            
        case _ => throw new Exception("ill-typed where: non-df or non-criterion input to term")

    case TmUnqWhere(t1, c1) => (typeOf(gamma, g_agg, t1), c1) match
        case (TyDF(cols), Crit(key, tau, EQ)) =>

            if (!(cols.contains(key))) {
                throw new Exception("ill-typed unqwhere: criterion contains column " + key + ", but " + key + " not in df")
            } else { cols(key) match
                case TyCol(ctau, Ucol) =>
                    if (ctau != typeOf(gamma, g_agg, tau)) { 
                        throw new Exception("ill-typed unqwhere: criterion expects different type on column " + key + " than is present in df")
                    }
                
                // unqwhere called on where, case (1)
                case TyCol(ctau, _) => throw new Exception("ill-typed unqwhere: applied to non-unique column " + key)
                case _ => throw new Exception("malformed columns - null error")
            }
            
            return TyOpt( R( TyDF(cols) ) )

        // unqwhere called on where, case (2)
        case (TyDF(cols), c1) => throw new Exception("ill-typed unqwhere: requires base EQ criterion input")
        case _ => throw new Exception("ill-typed where: non-df or non-criterion input to term")


    case TmGroupBy(df1, labels, gb) => typeOf(gamma, g_agg, df1) match 
        case TyDF(cols1) => try {
            var ndf: LinkedHashMap[String, Type] = LinkedHashMap()
            labels.foreach{ label => label match
                case (Some(agg), l) => cols1(l) match 
                    case TyCol(tau, kappa) => lookup_agg((agg, TyCol(tau, kappa)), g_agg) match
                        case Some(ntau) => ndf = ndf.++(Map(agg_to_string(label) -> TyCol(ntau, kappa)))
                        case None => throw new Exception("aggregator " + agg.toString + " cannot be applied to column with type " + tau.toString)
                    case _ => throw new Exception("null group by typing exception")
                
                case (None, l) => cols1(l) match 
                    case TyCol(tau, kappa) => 
                        if (gb.contains(l)) {
                            if (gb.length == 1 && kappa != Ocol) {
                                ndf = ndf.++(Map(l -> TyCol(tau, Ucol)))
                            } else {
                                ndf = ndf.++(Map(l -> TyCol(tau, kappa)))
                            }
                        } else { throw new Exception("column " + l + " isn't grouping and requires an aggregator") }
                    case _ => throw new Exception("null group by typing exception")
                }

            gb.foreach{ label =>
                if (!(cols1.contains(label))) {
                    throw new Exception("column " + label + " is grouping but isn't contained in df")
                }
            }
            return TyDF(ndf)

        } catch { case e => throw new Exception("ill-typed group by: " + e) }

        case _ => throw new Exception("ill-typed group by: requires df input")
    
}


// ------- evaluation


def isV(t: Term): Boolean = 
    var isval = true
    t match {
        case TmBool(_) | TmInt(_) | TmFloat(_) | TmString(_) | TmNone(_) => true
        case TmSome(t1) => isV(t1)
        case TmCol(arr, k) =>
            arr.foreach{ t1 => 
                if !(isV(t1)) then isval = false // using workaround b/c foreach is a nested anonymous fxn apparently
            }
            return isval
            
        case TmRec(rd) =>
            rd.keys.foreach{ t1 => 
                if !(isV(rd(t1))) then isval = false
            }
            return isval
        
        case TmDF(cols) =>
            cols.keys.foreach{ t1 => 
                if !(isV(cols(t1))) then isval = false
            }
            return isval
        
        case _ => false
    }

def infer_type(arr: Array[Term]): Type = 
    if (arr.length > 0) {
        arr(0) match
            case TmNone(tau) => TyOpt(tau)
            case TmSome(t1) => t1 match
                case TmInt(_) => TyOpt(TyInt)
                case TmFloat(_) => TyOpt(TyFloat)
                case TmString(_) => TyOpt(TyString)
                case TmBool(_) => TyOpt(TyBool)
                case _ => throw new Exception("runtime error: non-col input to agg (SHOULD NOT OCCUR)")
            case TmInt(_) => TyInt
            case TmFloat(_) => TyFloat
            case TmString(_) => TyString
            case TmBool(_) => TyBool
            case _ => throw new Exception("runtime error: non-col input to agg (SHOULD NOT OCCUR)")

    } else { throw new Exception("runtime error: cannot aggregate an empty column") }
    

def perform_agg(agg: Agg, arr: Array[Term]) : Term = 
    var seen = false
    agg match
        case Max => infer_type(arr) match 
            case TyInt => 
                var max : Int = 0
                arr.foreach{tm => tm match 
                    case TmInt(i) =>
                        if (!(seen) || max < i) { max = i; seen = true }
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmInt(max)
            case TyFloat => 
                var max : Float = 0
                arr.foreach{tm => tm match 
                    case TmFloat(f) =>
                        if (!(seen) || max < f) { max = f; seen = true }
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmFloat(max)
            case TyString => 
                var max : String = ""
                arr.foreach{tm => tm match 
                    case TmString(s) =>
                        if (!(seen) || max < s) { max = s; seen = true }
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmString(max)
            case TyBool => 
                var max : Boolean = false
                arr.foreach{tm => tm match 
                    case TmBool(b) =>
                        if (!(seen) || max < b) { max = b; seen = true }
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmBool(max)
            case TyOpt(TyInt) => 
                var max : Int = 0
                arr.foreach{tm => tm match 
                    case TmSome(TmInt(i)) =>
                        if (!(seen) || max < i) { max = i; seen = true }
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (seen) { return TmSome(TmInt(max)) } else { return TmNone(TyInt) }
            case TyOpt(TyFloat) => 
                var max : Float = 0.0
                arr.foreach{tm => tm match 
                    case TmSome(TmFloat(f)) =>
                        if (!(seen) || max < f) { max = f; seen = true }
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (seen) { return TmSome(TmFloat(max)) } else { return TmNone(TyFloat) }
            case TyOpt(TyString) => 
                var max : String = ""
                arr.foreach{tm => tm match 
                    case TmSome(TmString(s)) =>
                        if (!(seen) || max < s) { max = s; seen = true }
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (seen) { return TmSome(TmString(max)) } else { return TmNone(TyString) }
            case TyOpt(TyBool) => 
                var max : Boolean = false
                arr.foreach{tm => tm match 
                    case TmSome(TmBool(b)) =>
                        if (!(seen) || max < b) { max = b; seen = true }
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (seen) { return TmSome(TmBool(max)) } else { return TmNone(TyBool) }
            case _ => throw new Exception("agg pattern matching -- null error")
            
        case Min => infer_type(arr) match 
            case TyInt => 
                var min : Int = 0
                arr.foreach{tm => tm match 
                    case TmInt(i) =>
                        if (!(seen) || min > i) { min = i; seen = true }
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmInt(min)
            case TyFloat => 
                var min : Float = 0
                arr.foreach{tm => tm match 
                    case TmFloat(f) =>
                        if (!(seen) || min > f) { min = f; seen = true }
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmFloat(min)
            case TyString => 
                var min : String = ""
                arr.foreach{tm => tm match 
                    case TmString(s) =>
                        if (!(seen) || min > s) { min = s; seen = true }
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmString(min)
            case TyBool => 
                var min : Boolean = false
                arr.foreach{tm => tm match 
                    case TmBool(b) =>
                        if (!(seen) || min > b) { min = b; seen = true }
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmBool(min)
            case TyOpt(TyInt) => 
                var max : Int = 0
                arr.foreach{tm => tm match 
                    case TmSome(TmInt(i)) =>
                        if (!(seen) || max < i) { max = i; seen = true }
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (seen) { return TmSome(TmInt(max)) } else { return TmNone(TyInt) }
            case TyOpt(TyFloat) => 
                var max : Float = 0.0
                arr.foreach{tm => tm match 
                    case TmSome(TmFloat(f)) =>
                        if (!(seen) || max < f) { max = f; seen = true }
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (seen) { return TmSome(TmFloat(max)) } else { return TmNone(TyFloat) }
            case TyOpt(TyString) => 
                var min : String = ""
                arr.foreach{tm => tm match 
                    case TmSome(TmString(s)) =>
                        if (!(seen) || min > s) { min = s; seen = true }
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (seen) { return TmSome(TmString(min)) } else { return TmNone(TyString) }
            case TyOpt(TyBool) => 
                var min : Boolean = false
                arr.foreach{tm => tm match 
                    case TmSome(TmBool(b)) =>
                        if (!(seen) || min > b) { min = b; seen = true }
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (seen) { return TmSome(TmBool(min)) } else { return TmNone(TyBool) }
            case _ => throw new Exception("agg pattern matching -- null error")

        case Mean => infer_type(arr) match 
            case TyInt => 
                var mean : Float = 0
                arr.foreach{tm => tm match 
                    case TmInt(i) => mean = mean + i
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmFloat(mean / arr.length)
            case TyFloat => 
                var mean : Float = 0
                arr.foreach{tm => tm match 
                    case TmFloat(f) => mean = mean + f
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                return TmFloat(mean / arr.length)
            case TyOpt(TyInt) => 
                var mean : Float = 0; var nonNull = 0
                arr.foreach{tm => tm match 
                    case TmSome(TmInt(i)) => mean = mean + i; nonNull += 1
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (nonNull > 0) { return TmSome(TmFloat(mean / nonNull)) } else { return TmNone(TyFloat) }
            case TyOpt(TyFloat) => 
                var mean : Float = 0; var nonNull = 0
                arr.foreach{tm => tm match 
                    case TmSome(TmFloat(f)) => mean = mean + f; nonNull += 1
                    case TmNone(_) => // pass
                    case _ => throw new Exception("incorrect agg -- null error")
                }
                if (nonNull > 0) { return TmSome(TmFloat(mean / nonNull)) } else { return TmNone(TyFloat) }
            case _ => throw new Exception("agg pattern matching -- null error (should be caught in type checking)")
        
        case Count => return TmInt(arr.length)


def unwrap(tm: Term) : Term = tm match 
    case TmSome(tm1) => unwrap(tm1)
    case tm1 => tm1

def compare_terms(tm1: Term, tm2: Term) : Boolean = (unwrap(tm1), unwrap(tm2)) match
    case (TmNone(_), _) => false
    case (_, TmNone(_)) => true
    case (TmInt(t1), TmInt(t2)) => t1 > t2
    case (TmInt(t1), TmFloat(t2)) => t1 > t2
    case (TmFloat(t1), TmInt(t2)) => t1 > t2
    case (TmFloat(t1), TmFloat(t2)) => t1 > t2
    case (TmString(t1), TmString(t2)) => t1 > t2
    case (TmBool(t1), TmBool(t2)) => t1 > t2
    case (_, _) => throw new Exception("eval error in groupby: compare_terms called on nonmatching terms")

def key_to_string(arr: Array[Term]) : String = {
    var str : String = ""
    arr.foreach{ tm => str += str + unparse(tm) }

    return str
}


def DF_to_Array(df: LinkedHashMap[String, Term]) : Array[LinkedHashMap[String, Term]] = 
    var arr : Array[LinkedHashMap[String, Term]] = Array()
    val col_arr = df.keys.toArray
    df(col_arr(0)) match 
        case TmCol(arr1, _) => 
            for (i <- 0 until arr1.length) {
                var rd : LinkedHashMap[String, Term] = LinkedHashMap()
                col_arr.foreach{ key => df(key) match
                    case TmCol(arr1, _) => rd = rd.++(Map(key -> arr1(i)))
                    case _ => throw new Exception("runtime error: df does not contain columns -- null error")
                }

                arr = arr :+ rd
            }

            return arr
        case _ => throw new Exception("runtime error: df does not contain columns -- null error")

def Array_to_DF(arr: Array[LinkedHashMap[String, Term]], keys: Array[String]) : LinkedHashMap[String, Term] = 
    var df : LinkedHashMap[String, Term] = LinkedHashMap()
    keys.foreach{ key => 
        df = df.++(Map(key -> TmCol(Array(), Ocol))) // kappas no longer necessary in eval -- null
    }
    for (i <- 0 until arr.length) {
        arr(i).keys.foreach{ key => 
            df(key) match
                case TmCol(col, _) => 
                    df = df.++(Map(key -> TmCol(col :+ arr(i)(key), Ocol)))
                case _ => throw new Exception("array to df -- null error")
        }
    }

    return df

def satisfies(rd: LinkedHashMap[String, Term], c: Criterion) : Boolean = c match {
    case Crit(label, tm, comp) => rd(label) match
        case TmSome(in) => (in, comp, tm) match
            case (TmInt(i1), GT, TmInt(i2)) => i1 > i2 
            case (TmInt(i1), EQ, TmInt(i2)) => i1 == i2 
            case (TmInt(i1), LT, TmInt(i2)) => i1 < i2
            case (TmFloat(i1), GT, TmFloat(i2)) => i1 > i2 
            case (TmFloat(i1), EQ, TmFloat(i2)) => i1 == i2 
            case (TmFloat(i1), LT, TmFloat(i2)) => i1 < i2
            case (TmString(i1), GT, TmString(i2)) => i1 > i2 
            case (TmString(i1), EQ, TmString(i2)) => i1 == i2 
            case (TmString(i1), LT, TmString(i2)) => i1 < i2
            case (TmBool(i1), GT, TmBool(i2)) => i1 > i2 
            case (TmBool(i1), EQ, TmBool(i2)) => i1 == i2 
            case (TmBool(i1), LT, TmBool(i2)) => i1 < i2
            case _ => throw new Exception("runtime error: criterion does not match record -- null error")
        case TmNone(_) => false

        case in => (in, comp, tm) match
            case (TmInt(i1), GT, TmInt(i2)) => i1 > i2 
            case (TmInt(i1), EQ, TmInt(i2)) => i1 == i2 
            case (TmInt(i1), LT, TmInt(i2)) => i1 < i2
            case (TmFloat(i1), GT, TmFloat(i2)) => i1 > i2 
            case (TmFloat(i1), EQ, TmFloat(i2)) => i1 == i2 
            case (TmFloat(i1), LT, TmFloat(i2)) => i1 < i2
            case (TmString(i1), GT, TmString(i2)) => i1 > i2 
            case (TmString(i1), EQ, TmString(i2)) => i1 == i2 
            case (TmString(i1), LT, TmString(i2)) => i1 < i2
            case (TmBool(i1), GT, TmBool(i2)) => i1 > i2 
            case (TmBool(i1), EQ, TmBool(i2)) => i1 == i2 
            case (TmBool(i1), LT, TmBool(i2)) => i1 < i2
            case _ => throw new Exception("runtime error: criterion does not match record -- null error")

    case CNot(c1) => !(satisfies(rd, c1))
    case CAnd(c1, c2) => (satisfies(rd, c1) && satisfies(rd, c2))
    case COr(c1, c2) => (satisfies(rd, c1) || satisfies(rd, c2))
}




def bigStep(t: Term, vars: TermEnv): Term = t match {
    case TmBool(b) => TmBool(b)
    case TmInt(n) => TmInt(n)
    case TmFloat(f) => TmFloat(f)
    case TmString(s) => TmString(s)

    case TmRead(file, etau) => file match
        case TmString(fileName) => return read_csv(fileName, etau)
        case _ => throw new Exception("read -- null error")
    case TmWrite(tm, file) => (bigStep(tm, vars), file) match
        case (df, TmString(fileName)) => 
            write_csv(df, fileName)
            return TmBool(true)
        case _ => throw new Exception("write -- non-null error")
    case TmUnwrap(tm) => bigStep(tm, vars) match
        case TmSome(tm1) => return tm1
        case TmNone(_) => throw new Exception("runtime error: tried to unwrap None")
        case _ => throw new Exception("N operator -- null error")

    case TmVar(x) => tm_lookup(x, vars) match
        case Some(tm) => return tm
        case None => throw new Exception("unassigned variable referenced (runtime) -- should never happen")

    case TmSome(t1) => bigStep(t1, vars) match
        case v1 if isV(v1) => TmSome(v1)
        case _ => throw new Exception( "incorrect eval: TmSome" )
    case TmNone(tau) => TmNone(tau)

    
    case TmCol(col, k) => col.map(bigStep(_, vars)) match 
        case vcol if vcol.forall(t => isV(t)) => TmCol(vcol, k)
        case _ => throw new Exception("incorrect eval: col constructor")

    case TmColIndex(col, ind) => (bigStep(col, vars), bigStep(ind, vars)) match
        case ( TmCol(arr, k), TmInt(i) ) if isV(TmCol(arr, k)) => try {
            return arr(i)
        } catch { case e => throw new Exception("runtime error: colindex out of range")}

        case _ => throw new Exception("incorrect eval: colindex")

    case TmRec(rd) => rd.values.map(bigStep(_, vars)) match
        case vrd if vrd.forall(t => isV(t)) => 
            var nrd: LinkedHashMap[String, Term] = LinkedHashMap()
            rd.keys.foreach{ label =>
                nrd = nrd.++(Map(label -> bigStep(rd(label), vars)))   
            }
            return TmRec(nrd)
        
        case _ => throw new Exception("incorrect eval: rec constructor")

    case TmRecSelect(rd, key) => bigStep(rd, vars) match
        case TmRec(vrd) if isV(TmRec(vrd)) => vrd(key)
        case _ => throw new Exception("incorrect eval: rec select")

    case TmDF(df) => df.values.map(bigStep(_, vars)) match
        case vdf if vdf.forall(t => isV(t)) => 
            var ndf: LinkedHashMap[String, Term] = LinkedHashMap()
            var len = -1
            
            df.keys.foreach{ label => bigStep(df(label), vars) match
                case TmCol(arr, k) => 
                    if (len == -1) {
                        len = arr.length
                    } else if (len != arr.length) {
                        throw new Exception("runtime error: df contains cols of different lengths")
                    }

                    ndf = ndf.++(Map(label -> TmCol(arr, k)))   
                case _ => throw new Exception("df mistype in evaluation -- null error")

            }
            return TmDF(ndf)
        
        case _ => throw new Exception("incorrect eval: df constructor")

    case TmDFSelect(df, key) => bigStep(df, vars) match
        case TmDF(vdf) if isV(TmDF(vdf)) => vdf(key)
        case _ => throw new Exception("incorrect eval: df select")

    case TmDFInsert(df, label, col) => (bigStep(df, vars), bigStep(col, vars)) match
        case (TmDF(df), TmCol(arr, k)) if (isV(TmDF(df)) && isV(TmCol(arr, k))) => 
            val col_arr = df.keys.toArray
            if (col_arr.length != 0) {
                df(col_arr(0)) match 
                    case TmCol(arr1, _) => 
                        if (arr.length != arr1.length) { throw new Exception("runtime error: inserting column of mismatched len into df") }
                    case _ => throw new Exception("runtime error: df does not contain columns -- null error")

            }
            return TmDF(df.++(Map(label -> TmCol(arr, k))))
        case _ => throw new Exception("incorrect eval: df insert")

    
    case TmAgg(agg, t1) => bigStep(t1, vars) match 
        case TmCol(arr, _) => perform_agg(agg, arr)
        case _ => throw new Exception("incorrect eval: agg")

    case TmProj(df, labels) => bigStep(df, vars) match
        case TmDF(cols) => 
            var ndf: LinkedHashMap[String, Term] = LinkedHashMap()
            labels.foreach{ label =>
                ndf = ndf.++(Map(label -> cols(label)))
            }

            return TmDF(ndf)
        case _ => throw new Exception("incorrect eval: proj")

    case TmUnion(df1, df2) => (bigStep(df1, vars), bigStep(df2, vars)) match 
        case (TmDF(cols1), TmDF(cols2)) => 
            val set1 = DF_to_Array(cols1).toSet
            val set2 = DF_to_Array(cols2).toSet
            val keys = cols1.keys.toArray

            return TmDF(Array_to_DF((set1.union(set2)).toArray, keys))
        case _ => throw new Exception("incorrect eval: union")
    
    case TmIntersection(df1, df2) => (bigStep(df1, vars), bigStep(df2, vars)) match 
        case (TmDF(cols1), TmDF(cols2)) => 
            val set1 = DF_to_Array(cols1).toSet
            val set2 = DF_to_Array(cols2).toSet
            val keys = cols1.keys.toArray

            return TmDF(Array_to_DF((set1.intersect(set2)).toArray, keys))
        case _ => throw new Exception("incorrect eval: intersection")
    
    case TmDiff(df1, df2) => (bigStep(df1, vars), bigStep(df2, vars)) match 
        case (TmDF(cols1), TmDF(cols2)) => 
            val set1 = DF_to_Array(cols1).toSet
            val set2 = DF_to_Array(cols2).toSet
            val keys = cols1.keys.toArray

            return TmDF(Array_to_DF((set1.diff(set2)).toArray, keys))
        case _ => throw new Exception("incorrect eval: diff")
    
    case TmCross(df1, df2) => (bigStep(df1, vars), bigStep(df2, vars)) match
        case (TmDF(cols1), TmDF(cols2)) => 
            var ncols2 : LinkedHashMap[String, Term] = LinkedHashMap()
            cols2.keys.foreach{ key =>
                if (cols1.contains(key)) {
                    ncols2 = ncols2.++(Map(key+"_1" -> cols2(key)))
                } else {
                    ncols2 = ncols2.++(Map(key -> cols2(key)))
                }
            }

            val arr1 = DF_to_Array(cols1)
            val arr2 = DF_to_Array(ncols2)
            var cross : Array[LinkedHashMap[String, Term]] = Array()
            var keys = cols1.keys.toArray ++ ncols2.keys.toArray

            arr1.foreach{ rd1 => 
                arr2.foreach { rd2 => 
                    cross = cross :+ (rd1 ++ rd2)
                }
            }

            return TmDF(Array_to_DF(cross, keys))
        case _ => throw new Exception("incorrect eval: cross")
    
    case TmJoin(df1, df2, on) => (bigStep(df1, vars), bigStep(df2, vars)) match
        case (TmDF(cols1), TmDF(cols2)) => 
            var ncols2 : LinkedHashMap[String, Term] = LinkedHashMap()
            cols2.keys.foreach{ key =>
                if (cols1.contains(key) && !(on.contains(key))) {
                    ncols2 = ncols2.++(Map(key+"_1" -> cols2(key)))
                } else {
                    ncols2 = ncols2.++(Map(key -> cols2(key)))
                }
            }

            var arr1 = DF_to_Array(cols1)
            var arr2 = DF_to_Array(ncols2)
            var join : Array[LinkedHashMap[String, Term]] = Array()
            var keys = cols1.keys.toArray ++ ncols2.keys.toArray
            arr1.foreach { rd1 => 
                arr2.foreach { rd2 => 
                    var matching = true
                    var joined : LinkedHashMap[String, Term] = LinkedHashMap()
                    on.foreach{ key => 
                        (rd1(key), rd2(key)) match
                        case (i, j) if (i == j) => joined = joined.++(Map(key -> i))
                        case (TmSome(i), j) if (i == j) => joined.++(Map(key -> i))
                        case (i, TmSome(j)) if (i == j) => joined.++(Map(key -> i))
                        case (_, _) => matching = false
                        
                    }

                    if (matching) { join = join :+ (rd1 ++ rd2 ++ joined) }
                }
            }

            return TmDF(Array_to_DF(join, keys))
        case _ => throw new Exception("incorrect eval: join")

    case TmWhere(df1, c1) => bigStep(df1, vars) match
        case TmDF(cols1) =>
            val arr1 = DF_to_Array(cols1)
            var where : Array[LinkedHashMap[String, Term]] = Array()
            val keys = cols1.keys.toArray

            arr1.foreach{ rd1 => 
                if (satisfies(rd1, c1)) { where = where :+ rd1 }
            }

            return TmDF(Array_to_DF(where, keys))

        case _ => throw new Exception("incorrect eval: where") 

    case TmUnqWhere(df1, c1) => bigStep(df1, vars) match
        case TmDF(cols1) =>
            val arr1 = DF_to_Array(cols1)
            var where : Array[LinkedHashMap[String, Term]] = Array()
            var found = false

            arr1.foreach{ rd1 => 
                if (satisfies(rd1, c1)) { where = where :+ rd1 }
            }
            
            if (where.length > 0) { 
                return TmSome(TmRec(where(0)))
            } else { 
                return TmNone(TyInt)
            }

        case _ => throw new Exception("incorrect eval: unqwhere") 

    
    case TmGroupBy(df1, labels, gb) => bigStep(df1, vars) match
        case TmDF(cols1) => 
            val arr1 = DF_to_Array(cols1)
            var grouping : collection.mutable.Map[String, Array[Term]] = collection.mutable.Map()

            arr1.foreach{rd1 => 
                var tms : Array[Term] = Array()
                gb.foreach { gb_label => tms = tms :+ rd1(gb_label) }
                val key = key_to_string(tms)
                var new_val : Array[Term] = Array()

                if (grouping.contains(key)) {
                    grouping(key).lazyZip(labels).foreach { (gval, label) => label match
                        case (Some(Max), l) => 
                            if (compare_terms(rd1(l), gval)) {
                                new_val = new_val :+ rd1(l)
                            } else {
                                new_val = new_val :+ gval
                            }
                        case (Some(Min), l) => 
                            if (compare_terms(rd1(l), gval)) {
                                new_val = new_val :+ gval
                            } else {
                                new_val = new_val :+ rd1(l)
                            }
                        case (Some(Mean), l) => throw new Exception("unimplemented")

                        case (Some(Count), l) => gval match
                            case TmInt(n) => new_val = new_val :+ TmInt(n+1)
                            case _ => throw new Exception("null error in groupby -- count")

                        case (None, l) => new_val = new_val :+ rd1(l)
                    }

                    // grouping.keys.foreach(k => println(k))
                    // new_val.foreach(v => println(v))

                    grouping(key) = new_val

                } else {
                    labels.foreach { label => label match
                        case (Some(Mean), l) => throw new Exception("unimplmented")
                        case (Some(Count), l) => new_val = new_val :+ TmInt(1)
                        case (_, l) => new_val = new_val :+ rd1(l)
                    }

                    grouping.put(key, new_val)
                }
            }

            var new_arr : Array[LinkedHashMap[String, Term]] = Array()
            val keys = labels.map(agg_to_string)
            grouping.values.foreach { gval =>
                var grouped_rd : LinkedHashMap[String, Term] = LinkedHashMap()
                gval.lazyZip(labels).foreach{ (v, agg) => grouped_rd.put(agg_to_string(agg), v) }
                new_arr = new_arr :+ grouped_rd
            }

            return TmDF(Array_to_DF(new_arr, keys))

        case _ => throw new Exception("incorrect eval: groupby")

}

def printType(gamma : TypeEnv, g_agg: AggTypeEnv, tm : Term, name: String) = {
    try {
        println("\nType checking term " + name + ":") 
        println(typeOf(gamma, g_agg, tm))
    } catch { case e => println(e)}
}

def printTerm(tm: Term) : String = tm match {
    case TmBool(b) => "TmBool(" + b.toString + ")"
    case TmInt(n) => "TmInt(" + n.toString + ")"
    case TmFloat(f) => "TmFloat(" + f.toString + ")"
    case TmString(s) => "TmString(" + s + ")"

    case TmVar(varName) => varName

    case TmSome(t1: Term) => "TmSome(" + printTerm(t1) + ")"
    case TmNone(tau:Type) => "TmNone"

    case TmCol(col: Array[Term], k:Kappa) => 
        var out = "TmCol("
        col.foreach{ tm1 => out += printTerm(tm1) + "," }
        return out + ")"

    case TmRec(rd: LinkedHashMap[String,Term]) =>
        var out = "TmRec("
        rd.keys.foreach{ key => out += key + " -> " + printTerm(rd(key)) + "," }
        return out + ")"

    case TmDF(df: LinkedHashMap[String, Term]) =>
        var out = "TmDF(\n"
        df.keys.foreach{ key => out += key + " -> " + printTerm(df(key)) + "\n" }
        return out + ")"
    
    case _ => return tm.toString

}

def typeAndEval(gamma : TypeEnv, g_agg: AggTypeEnv, vars: TermEnv, tm : Term, name: String) = {
    try {
        println("\nType checking term " + name + ":") 
        println(typeOf(gamma, g_agg, tm))
        println("Type checking succeeded, evaluating:") 
        println(printTerm(bigStep(tm, vars)))
        
    } catch { case e => println("Evaluation errored out: " + e)}
}



@main def test(): Unit = {
    var gamma: TypeEnv = Map()
    var g_agg: AggTypeEnv = Map((Mean, TyCol(TyInt, Ucol)) -> TyFloat, (Mean, TyCol(TyInt, Col)) -> TyFloat, (Mean, TyCol(TyInt, Ocol)) -> TyOpt(TyFloat), 
                                (Mean, TyCol(TyFloat, Ucol)) -> TyFloat, (Mean, TyCol(TyFloat, Col)) -> TyFloat, (Mean, TyCol(TyFloat, Ocol)) -> TyOpt(TyFloat),
                                (Max, TyCol(TyInt, Ucol)) -> TyInt, (Max, TyCol(TyInt, Col)) -> TyInt, (Max, TyCol(TyInt, Ocol)) -> TyOpt(TyInt), 
                                (Max, TyCol(TyFloat, Ucol)) -> TyFloat, (Max, TyCol(TyFloat, Col)) -> TyFloat, (Max, TyCol(TyFloat, Ocol)) -> TyOpt(TyFloat),
                                (Max, TyCol(TyString, Ucol)) -> TyString, (Max, TyCol(TyString, Col)) -> TyString, (Max, TyCol(TyString, Ocol)) -> TyOpt(TyString),
                                (Min, TyCol(TyInt, Ucol)) -> TyInt, (Min, TyCol(TyInt, Col)) -> TyInt, (Min, TyCol(TyInt, Ocol)) -> TyOpt(TyInt), 
                                (Min, TyCol(TyFloat, Ucol)) -> TyFloat, (Min, TyCol(TyFloat, Col)) -> TyFloat, (Min, TyCol(TyFloat, Ocol)) -> TyOpt(TyFloat),
                                (Min, TyCol(TyString, Ucol)) -> TyString, (Min, TyCol(TyString, Col)) -> TyString, (Min, TyCol(TyString, Ocol)) -> TyOpt(TyString),
                                (Count, TyCol(TyInt, Ucol)) -> TyInt, (Count, TyCol(TyInt, Col)) -> TyInt, (Count, TyCol(TyInt, Ocol)) -> TyInt, 
                                (Count, TyCol(TyFloat, Ucol)) -> TyInt, (Count, TyCol(TyFloat, Col)) -> TyInt, (Count, TyCol(TyFloat, Ocol)) -> TyInt,
                                (Count, TyCol(TyString, Ucol)) -> TyInt, (Count, TyCol(TyString, Col)) -> TyInt, (Count, TyCol(TyString, Ocol)) -> TyInt,
                                (Count, TyCol(TyBool, Ucol)) -> TyInt, (Count, TyCol(TyBool, Col)) -> TyInt, (Count, TyCol(TyBool, Ocol)) -> TyInt,
                                )

    var vars: TermEnv = Map()

    def execute_line(code: String) = {

    try {
        val toks = scan(code)
        
        toks match 
            case TVar(varName) :: TAssign :: tl => 
                val tm = parse(tl)
                val tau = typeOf(gamma, g_agg, tm)
                val eval = bigStep(tm, vars)

                gamma = extend(varName, tau, gamma)
                vars = tm_extend(varName, eval, vars)

            case _ => 
                val tm = parse(toks)
                // println(unparse(tm))
                val tau = typeOf(gamma, g_agg, tm) // println("Parse succeeded with below term: Type checking:")
                val eval = bigStep(tm, vars) // println("Type checking succeeded with below type: Evaluating")

                println(tau)
                println(unparse(eval))

        } catch { case e => println(e) }
    }

    /*
    execute_line("b1", "3")
    execute_line("b2", "              \"hello gamers\"    ")
    execute_line("b3", "col([1, 2.0, \"3\", true], Col)")
    execute_line("b4", "col([some(1), some(2), none(I)], Ocol)")

    execute_line("c1", "colindex(col([1, 2, 3], Ucol), 2)")
    execute_line("c2", "colindex(col([1, 2, 3], Col), 2)")
    execute_line("c3", "colindex(col([1, 2, 3], Ocol), 2)")
    execute_line("c4", "colindex(col([some(1), some(2), none(I)], Ocol), 1)")
    execute_line("c5", "colindex(col([some(1), some(2), none(I)], Ocol), 2)")
    execute_line("c6", "colindex(col([some(1), some(2), none(I)], Ocol), 3)")

    execute_line("d1", "rec({\"a\" -> 3, \"b\" -> \"hello\", \"c\" -> true, \"d\" -> some(3.5)})")
    execute_line("d2", "df[{\"a\" -> col([1, 2, 3], Col), \"b\" -> col([some(1), some(2), none(I)], Ocol), \"c\" -> col([\"dog\", \"hi\", \"bye\"],Ucol)}]")
    execute_line("d3", "df[{\"a\" -> col([1, 2, 3], Col), \"b\" -> col([some(1), some(2), none(I)], Ocol), \"c\" -> col([\"dog\", \"hi\"],Ucol)}]")

    execute_line("e1", "dfselect(df[{\"a\" -> col([1, 2, 3], Col), \"b\" -> col([some(1), some(2), none(I)], Ocol), \"c\" -> col([\"dog\", \"hi\", \"bye\"],Ucol)}], \"b\")")
    execute_line("e2", "dfselect(df[{\"a\" -> col([1, 2, 3], Col), \"b\" -> col([some(1), some(2), none(I)], Ocol), \"c\" -> col([\"dog\", \"hi\", \"bye\"],Ucol)}], \"d\")")
    execute_line("e3", "dfinsert(df[{\"a\" -> col([1, 2, 3], Col), \"b\" -> col([some(1), some(2), none(I)], Ocol), \"c\" -> col([\"dog\", \"hi\", \"bye\"],Ucol)}], \"d\", col([true, false], Ocol))")
    execute_line("e4", "dfinsert(df[{\"a\" -> col([1, 2, 3], Col), \"b\" -> col([some(1), some(2), none(I)], Ocol), \"c\" -> col([\"dog\", \"hi\", \"bye\"],Ucol)}], \"d\", col([true, false], Ucol))")
    execute_line("e5", "dfinsert(df[{\"a\" -> col([1, 2, 3], Col), \"b\" -> col([some(1), some(2), none(I)], Ocol), \"c\" -> col([\"dog\", \"hi\", \"bye\"],Ucol)}], \"d\", col([some(true), none(B), some(false)], Ocol))")

    */

    gamma = extend("df1", typeOf(gamma, g_agg, TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(1), TmInt(2), TmInt(3)), Col),
                                    "b" -> TmCol(Array(TmSome(TmInt(1)), TmSome(TmInt(2)), TmNone(TyInt)), Ocol),
                                    "c" -> TmCol(Array(TmString("dog"), TmString("hi"), TmString("bye")), Ucol)))), gamma)
    vars = tm_extend("df1", TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(1), TmInt(2), TmInt(3)), Col),
                                    "b" -> TmCol(Array(TmSome(TmInt(1)), TmSome(TmInt(2)), TmNone(TyInt)), Ocol),
                                    "c" -> TmCol(Array(TmString("dog"), TmString("hi"), TmString("bye")), Ucol))), vars)

    gamma = extend("df2", typeOf(gamma, g_agg, TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(4), TmInt(2), TmInt(3)), Col),
                                    "b" -> TmCol(Array(TmSome(TmInt(1)), TmSome(TmInt(2)), TmNone(TyInt)), Ocol),
                                    "c" -> TmCol(Array(TmString("doooooog"), TmString("hi"), TmString("bye")), Ucol)))), gamma)
    vars = tm_extend("df2", TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(4), TmInt(2), TmInt(3)), Col),
                                    "b" -> TmCol(Array(TmSome(TmInt(1)), TmSome(TmInt(2)), TmNone(TyInt)), Ocol),
                                    "c" -> TmCol(Array(TmString("doooooog"), TmString("hi"), TmString("bye")), Ucol))), vars)

    gamma = extend("df3", typeOf(gamma, g_agg, TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(4), TmInt(2), TmInt(3)), Col),
                                    "c" -> TmCol(Array(TmString("doooooog"), TmString("hi"), TmString("bye")), Ucol)))), gamma)
    vars = tm_extend("df3", TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(4), TmInt(2), TmInt(3)), Col),
                                    "c" -> TmCol(Array(TmString("doooooog"), TmString("hi"), TmString("bye")), Ucol))), vars)

    gamma = extend("df3", typeOf(gamma, g_agg, TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(4), TmInt(2), TmInt(3)), Col),
                                    "c" -> TmCol(Array(TmString("doooooog"), TmString("hi"), TmString("bye")), Ucol)))), gamma)
    vars = tm_extend("df3", TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(4), TmInt(2), TmInt(3)), Col),
                                    "c" -> TmCol(Array(TmString("doooooog"), TmString("hi"), TmString("bye")), Ucol))), vars)

    gamma = extend("df4", typeOf(gamma, g_agg, TmDF(LinkedHashMap("b" -> TmCol(Array(TmSome(TmInt(2)), TmSome(TmInt(3))), Ocol),
                                    "d" -> TmCol(Array(TmBool(false), TmBool(true)), Ucol)))), gamma)
    vars = tm_extend("df4", TmDF(LinkedHashMap("b" -> TmCol(Array(TmSome(TmInt(2)), TmSome(TmInt(3))), Ocol),
                                    "d" -> TmCol(Array(TmBool(false), TmBool(true)), Ucol))), vars)

    gamma = extend("df6", typeOf(gamma, g_agg, TmDF(LinkedHashMap("b" -> TmCol(Array(TmSome(TmInt(2)), TmSome(TmInt(3))), Ocol),
                                    "d" -> TmCol(Array(TmBool(false), TmBool(true)), Ucol)))), gamma)
    vars = tm_extend("df6", TmDF(LinkedHashMap("b" -> TmCol(Array(TmInt(2), TmInt(3)), Col),
                                    "d" -> TmCol(Array(TmBool(false), TmBool(true)), Ucol))), vars)

    gamma = extend("df5", typeOf(gamma, g_agg, TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(1), TmInt(2), TmInt(3)), Col),
                                    "b" -> TmCol(Array(TmNone(TyInt), TmNone(TyInt), TmNone(TyInt)), Ocol),
                                    "c" -> TmCol(Array(TmString("dog"), TmString("hi"), TmString("bye")), Ucol)))), gamma)
    vars = tm_extend("df5", TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(1), TmInt(2), TmInt(3)), Col),
                                    "b" -> TmCol(Array(TmNone(TyInt), TmNone(TyInt), TmNone(TyInt)), Ocol),
                                    "c" -> TmCol(Array(TmString("dog"), TmString("hi"), TmString("bye")), Ucol))), vars)


    gamma = extend("df6", typeOf(gamma, g_agg, TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(1), TmInt(2), TmInt(3), TmInt(4), TmInt(5)), Col),
                                    "b" -> TmCol(Array(TmString("a"), TmString("a"), TmString("b"), TmString("b"), TmString("o")), Col)))), gamma)
    vars = tm_extend("df6", TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(1), TmInt(2), TmInt(3), TmInt(4), TmInt(5)), Col),
                                    "b" -> TmCol(Array(TmString("a"), TmString("a"), TmString("b"), TmString("b"), TmString("o")), Col))), vars)

    gamma = extend("df7", typeOf(gamma, g_agg, TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(1), TmInt(2), TmInt(3), TmInt(4), TmInt(5), TmInt(6)), Col),
                                    "b" -> TmCol(Array(TmSome(TmString("a")), TmSome(TmString("a")), TmNone(TyString), TmNone(TyString), TmSome(TmString("a")), TmNone(TyString)), Ocol),
                                    "c" -> TmCol(Array(TmBool(true), TmBool(false), TmBool(true), TmBool(false), TmBool(true), TmBool(false)), Col)))), gamma)
    vars = tm_extend("df7", TmDF(LinkedHashMap("a" -> TmCol(Array(TmInt(1), TmInt(2), TmInt(3), TmInt(4), TmInt(5), TmInt(6)), Col),
                                    "b" -> TmCol(Array(TmSome(TmString("a")), TmSome(TmString("a")), TmNone(TyString), TmNone(TyString), TmSome(TmString("a")), TmNone(TyString)), Ocol),
                                    "c" -> TmCol(Array(TmBool(true), TmBool(false), TmBool(true), TmBool(false), TmBool(true), TmBool(false)), Col))), vars)




    /*

    execute_line("f1", "agg(Mean, dfselect(df1, \"a\"))")
    execute_line("f2", "agg(Mean, dfselect(df1, \"b\"))")
    execute_line("f3", "agg(Mean, dfselect(df1, \"c\"))")
    execute_line("f4", "agg(Mean, dfselect(df1, \"d\"))")
    execute_line("f5", "agg(Mean, dfselect(df5, \"b\"))")

    execute_line("g1", "union(df1, df3)")
    execute_line("g2", "union(df1, df2)")
    execute_line("g3", "intersect(df1, df2)")
    execute_line("g4", "diff(df1, df2)")
    execute_line("g5", "diff(df1, df1)")
    execute_line("g6", "cross(df1, df4)")

    
    execute_line("g7", "join(df1, df4, [\"b\"])")
    execute_line("g8", "join(df1, df4, [\"b\", \"c\"])")
    execute_line("g9", "join(df1, df6, [\"b\"])")
    execute_line("g10", "join(df6, df1, [\"b\"])")
    execute_line("g11", "join(df6, df1, [\"b\", \"c\"])")
    execute_line("g12", "join(df1, df1, [\"a\", \"b\", \"c\"])")

    

    execute_line("h1", "where(df1, C(\"a\" > 2))")
    execute_line("h2", "where(df1, C(\"b\" > 0))")
    execute_line("h3", "where(df1, C(\"a\" > 4))")
    execute_line("h4", "where(df1, C(\"c\" > 0))")
    execute_line("h5", "where(df1, C(not(\"a\" > 4)))")
    execute_line("h6", "where(df2, C(or(\"a\" < 4, \"c\" > \"bye\")))")
    execute_line("h7", "where(df2, C(and(\"a\" < 4, \"c\" > \"bye\")))")

    execute_line("i1", "unqwhere(df2, C(and(\"a\" < 4, \"c\" > \"bye\")))")
    execute_line("i2", "unqwhere(df1, C(\"c\" == \"hi\"))")
    execute_line("i3", "unqwhere(df1, C(\"c\" == \"hello\"))")
    execute_line("i4", "where(df1, C(\"c\" == \"hi\"))")

    */

// col([recselect(N(student), "Exam_Score"), N(agg(Mean, dfselect(df2, "Exam_Score")))])

    var continue = true

    while (continue) {
        print("pingpong> ")
        var input : String = scala.io.StdIn.readLine()
        if (input == "exit") { 
            continue = false 
        } else {
            execute_line(input)
        }
    }

    // read("student_data_rec.csv", DF[{"FirstName" -> Ucol[S], "LastName" -> Col[S], "ID" -> Ocol[I], "State" -> Col[S], "Zip" -> Ucol[I]}])
    // df1 = read("student_data.csv", DF[{"FirstName" -> Col[S], "LastName" -> Col[S], "ID" -> Col[I], "State" -> Col[S], "Zip" -> Col[I]}])


    // students = read("student_data1.csv", DF[{"ID" -> Ucol[S], "Graduation_Year" -> Col[I], "Classes_Taken" -> Col[I], "Exam_Taken" -> Col[B], "Exam_Score" -> Ocol[F]}])
    // ids = read("names_ids.csv", DF[{"FirstName" -> Col[S], "LastName" -> Col[S], "ID" -> Ucol[S]}])


    
}


