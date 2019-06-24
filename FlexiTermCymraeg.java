/* ====================================================================
 * Copyright (c) 2016, Dr Irena Spasic
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met: 
 * 
 * 1. Redistributions of source code must retain the above copyright notice, this
 *    list of conditions and the following disclaimer.
 * 
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution. 
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * The views and conclusions contained in the software and documentation are those
 * of the authors and should not be interpreted as representing official policies, 
 * either expressed or implied, of the FreeBSD Project.
 *
 * Acknowledgements:
 * 
 * Jones, D. B., Robertson, P., Prys, G. (2015) Welsh language Lemmatizer API Service
 * [http://techiaith.cymru/api/lemmatizer/?lang=en]
 *
 * Jones, D. B., Robertson, P., Prys, G. (2015) Welsh language Parts-of-Speech Tagger API Service
 * [http://techiaith.cymru/api/parts-of-speech-tagger-api/?lang=en]
 *
 * Jones, D. B., Robertson, P., Prys, G. (2015) Welsh language Spelling and Grammar Checker API Service
 * [http://techiaith.cymru/api/cysill-ar-lein/?lang=en]
 *
 * ==================================================================== */

import java.io.File;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.InputStream;
import java.io.StringReader;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLEncoder;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.List;
import java.util.Iterator;
import java.sql.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.text.DecimalFormat;
import javax.net.ssl.HttpsURLConnection;

// --- import org.json classes
import org.json.JSONException;
import org.json.JSONObject;
import org.json.JSONTokener;

public class FlexiTermCymraeg {

// --- (global) database connection variables ---
private static Connection con;
private static String driver = "org.sqlite.JDBC";
private static String url = "jdbc:sqlite:flexitermcymraeg.sqlite";

// --- settings (default values) ---
private static String pattern = 
    "NN (NN | JJ)+|NN (NN | JJ)* IN NN (NN | JJ)*";
																							// --- POS pattern for term candidate selection
private static String stoplist = ".\\stoplist.txt";           								// --- stoplist location - modify the file content if necessary
private static int    max = 3;                                								// --- number of suggestions to seek via spellchecker - reduce for better similarity
private static int    min = 2;                                								// --- term frequency threshold: occurrence > min - increase for better precision
private static String apiPOSTaggerAddress = "https://api.techiaith.org/pos/v1/?";			// --- Techiaith POS Tagger API URL
private static String apiPOSTaggerKey = "485fb2e4-1536-4afc-a0e3-65ca28faf398";				// --- Techiaith POS Tagger API key
private static String apiLemmatizerAddress = "https://api.techiaith.org/lemmatizer/v1/?";	// --- Techiaith Lemmatizer API URL
private static String apiLemmatizerKey = "fa3cf0ac-5d9f-4ce9-ae0d-cae9db2ad28d";			// --- Techiaith Lemmatizer API key
private static String apiCysillOnlineAddress = "https://api.techiaith.org/cysill/v1/?";		// --- Techiaith CysillOnline (spell checker) API URL
private static String apiCysillOnlineKey = "c358ccd2-68f2-464f-a37a-b8a0249aac11";			// --- Techiaith CysillOnline (spell checker) API key

public enum TechiaithService {
	POSTAGGER, LEMMATIZER, SPELLCHECKER
}

public static void main(String[] args)
{
  try
  {
    // --- load settings
    loadSettings(".\\settings.txt");

    open();  // --- SQLite database connection

    Statement stmt  = con.createStatement();
    Statement stmt1 = con.createStatement();
    ResultSet rs, rs1;
    String query;

    stmt.execute("PRAGMA journal_mode = OFF;");

    // --- empty database
    query = "DELETE FROM data_document;"; stmt.execute(query);
    query = "DELETE FROM data_sentence;"; stmt.execute(query);
    query = "DELETE FROM data_token;"; stmt.execute(query);
    query = "DELETE FROM term_phrase;"; stmt.execute(query);
    query = "DELETE FROM term_normalised;"; stmt.execute(query);
    query = "DELETE FROM term_bag;"; stmt.execute(query);
    query = "DELETE FROM token;"; stmt.execute(query);
    query = "DELETE FROM token_similarity;"; stmt.execute(query);
    query = "DELETE FROM term_nested_aux;"; stmt.execute(query);
    query = "DELETE FROM term_nested;"; stmt.execute(query);
    query = "DELETE FROM term_termhood;"; stmt.execute(query);
    query = "DELETE FROM stopword;"; stmt.execute(query);

    // --- import stoplist
    loadStoplist(stoplist);

    // --- load & preprocess documents
    loadDocuments("./text");

    // --- start timing term recognition
    long startTime, endTime, runTime;
    startTime = System.currentTimeMillis();
    System.out.println("Start time: " + ((startTime % 86400000) / 3600000 + 1) + ":" + (startTime % 3600000) / 60000 + ":" + (startTime % 60000) / 1000);

    // ******************* EXTRACT NOUN PHRASES OF GIVEN STRUCTURE *******************

    // --- for each sentence
    query = "SELECT id, tags FROM data_sentence ORDER BY id;";
    System.out.println(query);
    rs = stmt.executeQuery(query);

    while (rs.next())
    {
      String sentence_id = rs.getString(1);  // --- sentence id
      String tags        = rs.getString(2);  // --- sentence tag pattern

      // --- NP pattern filter - for default pattern filter see declaration of 'pattern' at top of class
      Pattern r = Pattern.compile(pattern);
      Matcher m = r.matcher(tags);

      int p = 0; // --- phrase number

      // --- for each matching chunk
      while(m.find())
      {
        String chunk = m.group(0);                  // --- chunk tags
        String pre = tags.substring(0, m.start());  // --- the preceding tags
		
        int start  = whitespaces(pre)   + 1;        // --- start token position
        int length = whitespaces(chunk) + 1;        // --- chunk length in tokens
		
        // --- trim leading stop words
        while (length > 1)
        {
          query = "SELECT LOWER(token)"                                                                              + "\n" +
                  "FROM   data_token"                                                                                + "\n" +
                  "WHERE  sentence_id = '" + sentence_id + "'"                                                       + "\n" +
                  "AND    position = " + start                                                                       + "\n" +
                  "AND    (token LIKE '%-%-%' OR token LIKE 'unit%' or token LIKE 'area%' or token LIKE 'history'"   + "\n" +
                  "OR     (LOWER(token) IN (SELECT LOWER(word) FROM stopword)));";
          System.out.println(query);
          rs1 = stmt1.executeQuery(query);
          if (rs1.next())
          {
            String stopword = rs1.getString(1);
            start++;
            length--;
          }
          else break;
          rs1.close();
        }

        // --- trim trailing stop words
        while (length > 1)
        {
		  query = "SELECT LOWER(T.token)"                                                   + "\n" +
                  "FROM   data_token T, stopword S"                                         + "\n" +
                  "WHERE  sentence_id = '" + sentence_id + "'"                              + "\n" +
                  "AND    position = " + (start + length - 1)                               + "\n" +
                  "AND    (LOWER(T.token) = LOWER(S.word));";
          System.out.println(query);
          rs1 = stmt1.executeQuery(query);
          if (rs1.next())
          {
            String stopword = rs1.getString(1);
            length--;
          }
          else break;
          rs1.close();
        }

        if (1 < length && length < 8) // --- if still multiword phrase and not too long
        {
          p++;
          String phrase_id = sentence_id + "." + p;

          String phrase = "";
          query = "SELECT position, token"                          + "\n" +
                  "FROM   data_token"                               + "\n" +
                  "WHERE  sentence_id = '" + sentence_id + "'"      + "\n" +
                  "AND    " + start + " <= position"                + "\n" +
                  "AND    position < " + (start + length)           + "\n" +
                  "ORDER BY position ASC;";
          System.out.println(query);
          rs1 = stmt1.executeQuery(query);
          while (rs1.next()) phrase += " " + rs1.getString(2);
          phrase = phrase.substring(1);
          int last = phrase.length() - 1;
          if (phrase.charAt(last) == '.') phrase = phrase.substring(0, last);
          rs1.close();

          // --- ignore phrases that contain web concepts: email address, URL, #hashtag
          if (!(phrase.contains("@") || phrase.contains("#") || phrase.toLowerCase().contains("http") || phrase.toLowerCase().contains("www")))
          {
            query = "INSERT INTO term_phrase(id, sentence_id, token_start, token_length, phrase)\n" +
                    "VALUES ('" + phrase_id + "', '" + sentence_id + "', " + start + ", " + length + ", " + fixApostrophe(phrase) + ");";
            System.out.println(query);
            stmt1.execute(query);
          }
        }
      }
    }
    rs.close();

    // ******************* NORMALISE TERM CANDIDATES *******************

    // 1 --- remove punctuation, numbers and stop words
    // 2 --- remove any lowercase tokens shorter than 3 characters		LOWER(token) = token AND LENGTH(token) < 3
    // 3 --- lowercase each remaining token								SELECT LOWER(lemma)
    // 4 --- sort tokens alphabetically
    query = "SELECT id, sentence_id, token_start, token_length FROM term_phrase;";
    System.out.println(query);
    rs = stmt.executeQuery(query);
    while (rs.next())
    {
      String phrase_id   = rs.getString(1);
      String sentence_id = rs.getString(2);
      int    start       = rs.getInt(3);
      int    length      = rs.getInt(4);

      String normalised = "";
	  query = "SELECT LOWER(lemma)"                                    + "\n" +
              "FROM   data_token"                                      + "\n" +
              "WHERE  sentence_id = '" + sentence_id + "'"             + "\n" +
              "AND    " + start + " <= position"                       + "\n" +
              "AND    position < " + (start + length)                  + "\n" +
              "AND NOT (LOWER(token) = token AND LENGTH(token) < 3)"   + "\n" +
              "EXCEPT SELECT word FROM stopword"                       + "\n" +
              "ORDER BY LOWER(lemma) ASC;";
      System.out.println(query);
      rs1 = stmt1.executeQuery(query);
      while (rs1.next()) normalised += " " + rs1.getString(1);
      if (normalised.length() > 0) normalised = normalised.substring(1);
      normalised = normalised.replaceAll("\\.", "");   // --- e.g. U.K., Dr., St. -> UK, Dr, St
      System.out.println(normalised);
      rs1.close();

      query = "UPDATE term_phrase"                                      + "\n" +
              "SET    normalised = " + fixApostrophe(normalised)        + "\n" +
              "WHERE  id = '" + phrase_id + "';";
      System.out.println(query);
      stmt1.execute(query);
    }
    rs.close();

    // ******************* SELECT NORMALISED TERM CANDIDATES *******************
    query = "INSERT INTO term_normalised(normalised)"                   + "\n" +
            "SELECT DISTINCT normalised"                                + "\n" +
            "FROM   term_phrase"                                        + "\n" +
            "WHERE  LENGTH(normalised) > 5"                             + "\n" +
            "AND    normalised LIKE '% %';";
    System.out.println(query);
    stmt.execute(query);

    // ******************* TOKENISE NORMALISED TERM CANDIDATES *******************
    query = "SELECT rowid, normalised FROM term_normalised;";
    System.out.println(query);
    rs = stmt.executeQuery(query);
    while (rs.next())
    {
      int id = rs.getInt(1);
      String normalised = rs.getString(2) + " ";

      int len = 0;
      int t = -1;
      while ((t = normalised.indexOf(" ")) > 0)
      {
        String token = normalised.substring(0, t);
        normalised = normalised.substring(t+1);

        token = token.replaceAll("\\.", "");   // --- e.g. U.K., Dr., St. -> UK, Dr, St

        query = "INSERT INTO term_bag(id, token)\n" +
                "VALUES(" + id + ", " + fixApostrophe(token) + ");";
        System.out.println(query);
        stmt1.execute(query);

        len++;
      }

      query = "UPDATE term_normalised SET len = " + len + " WHERE rowid = " + id + ";";
      stmt1.execute(query);
    }
    rs.close();

    // ******************* SELECT DISTINCT TOKENS *******************
    query = "INSERT INTO token(token)\n" +
            "SELECT DISTINCT token FROM term_bag;";
    System.out.println(query);
    stmt.execute(query);

    // ******************* CALCULATE TOKEN SIMILARITY *******************
	// --- select all tokens for spell checking
    query = "SELECT token"                          + "\n" +
            "FROM   token"                          + "\n" +
            "WHERE  LENGTH(token) > 2 * " + max     + "\n" +
            "ORDER BY token ASC;";
    System.out.println(query);

    // --- process each token with CysillOnline (spell checker)
    rs = stmt.executeQuery(query);
    while (rs.next())
    {
      String token = rs.getString(1);
	  
	  //String suggestionString = useTechiaithService(TechiaithService.SPELLCHECKER, token);
	  //List<String> suggestions = suggestionString.contains("suggestions") ? Arrays.asList(suggestionString.substring(suggestionString.lastIndexOf("[")+1, suggestionString.indexOf("]")).replaceAll("\"", "").split(",")) : null;
	  
      List<String> suggestions = null;
      if (suggestions != null)
      {
        for (Iterator i = suggestions.iterator(); i.hasNext();)
        {
          String token2 = "" + i.next();  // --- NOTE: token < token2

          query = "INSERT INTO token_similarity(token1, token2)\n" +
                  "VALUES (" + fixApostrophe(token) + "," + fixApostrophe(token2) + ");";
          System.out.println(query);
          stmt1.execute(query);

          query = "INSERT INTO token_similarity(token1, token2)\n" +
                  "VALUES (" + fixApostrophe(token2) + "," + fixApostrophe(token) + ");";
          System.out.println(query);
          stmt1.execute(query);
        }
      }
    }
    rs.close();

    // --- create transitive closure
    Boolean closed = false;
    while (!closed)
    {
      closed = true;

      // --- if x ~ y, y ~ z & x != z & x !~ z, then add x ~ z
      query = "SELECT DISTINCT S1.token1, S2.token2"                + "\n" +
              "FROM   token_similarity S1, token_similarity S2"     + "\n" +
              "WHERE  S1.token2 =  S2.token1"                       + "\n" +
              "AND    S1.token1 <> S2.token2"                       + "\n" +
              "EXCEPT"                                              + "\n" +
              "SELECT token1, token2"                               + "\n" +
              "FROM   token_similarity;";
      System.out.println(query);
      rs = stmt.executeQuery(query);
      while (rs.next()) 
      {
        String token1 = rs.getString(1);
        String token2 = rs.getString(2);

        query = "INSERT INTO token_similarity(token1, token2)"      + "\n" +
                "VALUES (" + fixApostrophe(token1) + ", " + fixApostrophe(token2) + ");";
        System.out.println(query);
        stmt1.execute(query);

        closed = false;
      }
      rs.close();
    }

    // ******************* EXPAND TERMS WITH SIMILAR TOKENS *******************
    query = "INSERT INTO term_bag(id, token)"      + "\n" +
            "SELECT DISTINCT id, token2"           + "\n" +
            "FROM term_bag, token_similarity"      + "\n" +
            "WHERE token = token1;";
    System.out.println(query);
    stmt.execute(query);

    int total = 0;
    query = "SELECT MAX(rowid) FROM term_normalised;";
    System.out.println(query);
    rs = stmt.executeQuery(query);
    if (rs.next()) total = rs.getInt(1);
    rs.close();

    for (int id = 1; id <= total; id++)
    {
      String expanded = "";

      query = "SELECT token"                       + "\n" +
              "FROM   term_bag"                    + "\n" +
              "WHERE  id = " + id                  + "\n" +
              "ORDER BY token;";
      System.out.println(query);
      rs = stmt.executeQuery(query);
      while (rs.next())
      {
        expanded += " " + rs.getString(1);
      }
      rs.close();

      expanded = expanded.substring(1);

      query = "UPDATE term_normalised SET expanded = " + fixApostrophe(expanded) + " WHERE rowid = " + id + ";";
      System.out.println(query);
      stmt.execute(query);
    }

    // ******************* IDENTIFY TERM NESTEDNESS *******************
    for (int id = 1; id <= total; id++)
    {
      query = "SELECT token FROM term_bag WHERE id = " + id + ";";
      System.out.println(query);
      rs = stmt.executeQuery(query);
      query = "";
      while (rs.next()) 
      {
        String token = rs.getString(1);

        query += "\nINTERSECT\n" + 
                 "SELECT DISTINCT id FROM term_bag WHERE token = " + fixApostrophe(token) + " AND id <> " + id;
      }
      rs.close();

      if (query.length() > 0)
      {
        query = query.substring(11) + ";";
        System.out.println(query);
        rs = stmt.executeQuery(query);
        while (rs.next()) 
        {
          int parent = rs.getInt(1);
          query = "INSERT INTO term_nested_aux(parent, child)\n" +
                  "VALUES (" + parent + ", " + id + ");";
          System.out.println(query);
          stmt1.execute(query);
        }
      }
      rs.close();
    }

    query = "INSERT INTO term_nested(parent, child)"                               + "\n" +
            "SELECT DISTINCT N1.expanded, N2.expanded"                             + "\n" +
            "FROM   term_normalised N1, term_normalised N2, term_nested_aux A"     + "\n" +
            "WHERE  N1.rowid = A.parent"                                           + "\n" +
            "AND    N2.rowid = A.child"                                            + "\n" +
            "AND    N1.expanded <> N2.expanded;";
    System.out.println(query);
    stmt.execute(query);

    // ******************* CALCULATE TERMHOOD *******************
    query = "INSERT INTO term_termhood(expanded, len, s, nf)\n" +
            "SELECT DISTINCT expanded, len, 0, 0 FROM term_normalised;";
    System.out.println(query);
    stmt.execute(query);

    // --- calculate frequency of exact occurrence
    query = "SELECT N.expanded, COUNT(*)"                       + "\n" +
            "FROM   term_normalised N, term_phrase P"           + "\n" +
            "WHERE  N.normalised = P.normalised"                + "\n" +
            "GROUP BY N.expanded;";
    System.out.println(query);
    rs = stmt.executeQuery(query);
    while (rs.next()) 
    {
      String expanded = rs.getString(1);
      int    f = rs.getInt(2);

      query = "UPDATE term_termhood SET f = " + f + " WHERE expanded = " + fixApostrophe(expanded) + ";";
      System.out.println(query);
      stmt1.execute(query);
    }
    rs.close();

    // --- calculate the number of parent term candidates
    query = "SELECT child, COUNT(*)"     + "\n" +
            "FROM   term_nested"         + "\n" +
            "GROUP BY child;";
    System.out.println(query);
    rs = stmt.executeQuery(query);
    while (rs.next())
    {
      String child = rs.getString(1);
      int    s = rs.getInt(2);

      query = "UPDATE term_termhood SET s = " + s + " WHERE expanded = " + fixApostrophe(child) + ";";
      System.out.println(query);
      stmt1.execute(query);
    }
    rs.close();

    // --- calculate the frequency of nested occurrence
    query = "SELECT child, COUNT(*)"                                     + "\n" +
            "FROM   term_nested N, term_normalised C, term_phrase P"     + "\n" +
            "WHERE  N.parent = C.expanded"                               + "\n" +
            "AND    C.normalised = P.normalised"                         + "\n" +
            "GROUP BY child;";
    System.out.println(query);
    rs = stmt.executeQuery(query);
    while (rs.next()) 
    {
      String child = rs.getString(1);
      int    nf = rs.getInt(2);

      query = "UPDATE term_termhood SET nf = " + nf + " WHERE expanded = " + fixApostrophe(child) + ";";
      System.out.println(query);
      stmt1.execute(query);
    }
    rs.close();

    // --- add up frequencies: f(t)
    query = "UPDATE term_termhood SET f = f + nf;";
    System.out.println(query);
    stmt1.execute(query);

    // --- calculate C-value
    query = "SELECT expanded, len, f, s, nf FROM term_termhood;";
    System.out.println(query);
    rs = stmt.executeQuery(query);
    while (rs.next()) 
    {
      String expanded = rs.getString(1);
      int len = rs.getInt(2);
      int f   = rs.getInt(3);
      int s   = rs.getInt(4);
      int nf  = rs.getInt(5);

      double c = cValue(len, f, s, nf);

      query = "UPDATE term_termhood SET c = " + c + " WHERE expanded = " + fixApostrophe(expanded) + ";";
      System.out.println(query);
      stmt1.execute(query);
    }

    rs.close();

    // --- stop timing term recogntion
    endTime = System.currentTimeMillis();
    runTime = ((endTime - startTime) / 1000) ;// 60; // --- run time in minutes
    System.out.println("Term recognition done in " + runTime + " min.\n");

    // --- write results to output files
    export();
	
    con.commit();
    stmt.close();
    stmt1.close();

    close();  // --- SQLite database connection
  }
  catch(Exception e){e.printStackTrace();}
}
// ********************** END OF MAIN ***********************


// ----------------------------------------------------------
// --- 
// ----------------------------------------------------------
public static double cValue(int len, int f, double s, double nf)
{
  double c = f;

  if (s > 0) c -= nf / s;

  c *= Math.log(len);

  return c;
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- generalise tags
// ----------------------------------------------------------
public static String general(String tag)
{
    // if this is a multi tag (e.g. - CONJ+EXCL+PART+PRONREL) keep only the first tag unless one of the components is a kind of noun, adjective, or verb
    if (tag.contains("+")) {
        // if a kind of noun is found
        if(tag.startsWith("N") ||
           tag.contains("+N")) {
            return "NN";
        }
        // if a kind of adjective is found
        else if(tag.startsWith("ADJ") ||
                tag.contains("+ADJ")) {
            return "JJ";
        }
        // if no kind of noun or adjective is found then keep only the first tag
        else {
            tag = tag.substring(0,tag.indexOf("+")); // Remove all but this part of the if statement if returning to previous version of code is desired
        }
	}
	
	String gtag = tag;
    
	// replace tag with the most general tag where appropriate
	if (tag.length() <= 1		||
		tag.equals("punct")		||
		tag.equals("apostrophe")||
		tag.equals("EOS"))						gtag = "PUN";	// Punctuation
	else if (tag.equals("numeric"))				gtag = "NUMBER";// Number
	else if (tag.substring(0,1).equals("N") &&
			!tag.equals("NUMBER"))				gtag = "NN";	// Noun
	else if (tag.substring(0,1).equals("V"))	gtag = "VB";	// Verb
	else if (tag.substring(0,3).equals("ADJ"))	gtag = "JJ";	// Adjective (ADJ)
	else if (tag.substring(0,3).equals("ADV"))	gtag = "ADV";	// Adverb
	else if (tag.substring(0,3).equals("CAR"))	gtag = "CAR";	// Cardinal
	else if (tag.substring(0,3).equals("CPR") ||
			 tag.equals("PREP"))				gtag = "IN";	// Preposition (PREP)
	else if (tag.substring(0,3).equals("DET"))	gtag = "DT";	// Determiner (DET)
	else if (tag.substring(0,3).equals("ORD"))	gtag = "ORD";	// Ordinal
	else if (tag.substring(0,3).equals("PAR"))	gtag = "PART";	// Particle
	else if (tag.substring(0,3).equals("PRO"))	gtag = "PRO";	// Pronoun

	return gtag;
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- open database connection
// ----------------------------------------------------------
public static void open()
{
  System.out.println("\nDatabase.open(): open database connection\n");

  try
  {
    // --- load the postgresql jdbc driver
    Class.forName(driver);

    con = DriverManager.getConnection(url);
    con.setAutoCommit(false);
  }
  catch (SQLException ex)        {explain(ex);}
  catch (java.lang.Exception ex) {ex.printStackTrace();}
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- close database connection
// ----------------------------------------------------------
public static void close()
{
  System.out.println("\nDatabase.close(): close database connection");

  try {con.close();}
  catch (SQLException ex) {explain(ex);}
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- explain the SQL exception caught
// ----------------------------------------------------------
public static void explain(SQLException ex)
{
  System.out.println ("\n*** SQLException caught ***\n");

  while (ex != null) 
  {
    System.out.println("SQLState: " + ex.getSQLState());
    System.out.println("Message:  " + ex.getMessage());
    System.out.println("Vendor:   " + ex.getErrorCode());
    System.out.println("");

    ex = ex.getNextException();
  }
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- fix apostrophe, a special character in SQL, 
// --- so it can be imported (' --> '')
// ----------------------------------------------------------
private static String fixApostrophe(String inputString)
{
  if (inputString == null) return "NULL";

  String outputString = "";
  int i, l;

  l = inputString.length();

  for (i = 0; i < l; i++)
  {
    char c = inputString.charAt(i);
    outputString += c;
    if (c == '\'') outputString += "'";
  }

  return "'" + outputString + "'";
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- total # of whitespaces in a string
// ----------------------------------------------------------
private static int whitespaces(String inputString)
{
  if (inputString == null) return 0;
  else return inputString.length() - inputString.replaceAll(" ", "").length();
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- load setting from file (settings.txt), e.g.
// ----------------------------------------------------------
private static void loadSettings(String file)
{
  System.out.println("Loading settings from " + file + "...");
  File settings = new File(file);

  if (!settings.exists() || !settings.isFile())
  {
    System.out.println("Settings file " + file + " does not exist.");
    System.out.println("Using defaults values:");
    System.out.println("* pattern  					: " + pattern);
    System.out.println("* stoplist 					: " + stoplist);
    System.out.println("* max      					: " + max);
    System.out.println("* min      					: " + min);
	System.out.println("* apiPOSTaggerAddress		: " + apiPOSTaggerAddress);
	System.out.println("* apiPOSTaggerKey			: " + apiPOSTaggerKey);
	System.out.println("* apiLemmatizerAddress		: " + apiLemmatizerAddress);
	System.out.println("* apiLemmatizerKey			: " + apiLemmatizerKey);
	System.out.println("* apiCysillOnlineAddress	: " + apiCysillOnlineAddress);
	System.out.println("* apiCysillOnlineKey		: " + apiCysillOnlineKey);
  }
  else
  {
    try
    {
      // --- read settings from file
      BufferedReader in = new BufferedReader(new FileReader(settings));
      String line;

      while((line = in.readLine())!= null)
      {
        int i = line.indexOf(' ');
        if (i > 0)
        {
          String parameter = line.substring(0, i);
          String value = line.substring(i+1);

          // --- validate & initialise parameters
          if (parameter.equals("pattern"))
          {
            try
            {
              Pattern r = Pattern.compile(value);
              pattern = value;
            }
            catch(Exception e)
            {
              System.out.println("Invalid POS pattern: " + value);
              System.out.println("Using default: pattern = " + pattern);
            }
          }
          else if (parameter.equals("stoplist"))
          {
            File sl = new File(stoplist);

            if (!sl.exists() || !sl.isFile()) 
            {
              System.out.println("Stoplist file " + file + " does not exist.");
              System.out.println("Using default: stoplist = " + stoplist);
            }
            else stoplist = value;
          }
          else if (parameter.equals("max"))
          {
            try
            {
              int number = Integer.parseInt(value);

              if (0 < number && number < 10) max = number;
              else
              {
                System.out.println("Invalid max value: " + value);
                System.out.println("Using default: max = " + max);
              }
            }
            catch(Exception e)
            {
              System.out.println("Invalid max value: " + value);
              System.out.println("Using default: max = " + max);
            }
          }
          else if (parameter.equals("min"))
          {
            try
            {
              int number = Integer.parseInt(value);

              min = number;
            }
            catch(Exception e)
            {
              System.out.println("Invalid min value: " + value);
              System.out.println("Using default: min = " + min);
            }
          }
		  else if(parameter.equals("apiPOSTaggerAddress")) {
			  apiPOSTaggerAddress = value;
		  }
		  else if(parameter.equals("apiPOSTaggerKey")) {
			  apiPOSTaggerKey = value;
		  }
		  else if(parameter.equals("apiLemmatizerAddress")) {
			  apiLemmatizerAddress = value;
		  }
		  else if(parameter.equals("apiLemmatizerKey")) {
			  apiLemmatizerKey = value;
		  }
		  else if(parameter.equals("apiCysillOnlineAddress")) {
			  apiCysillOnlineAddress = value;
		  }
		  else if(parameter.equals("apiCysillOnlineKey")) {
			  apiCysillOnlineKey = value;
		  }
          else System.out.println("Invalid line: " + line);
        }
        else System.out.println("Invalid line: " + line);
      }
    }
    catch(Exception e){e.printStackTrace();}
  }
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- load stoplist from file into database
// ----------------------------------------------------------
private static void loadStoplist(String file)
{
  try
  {
    System.out.println("Loading stoplist from " + file + "...");

    Statement stmt = con.createStatement();

    File in = new File(file);

    if (!in.exists() || !in.isFile()) System.out.println("Invalid stoplist file: " + file);
    else 
    {
      // --- read stopwords from file
      BufferedReader fin = new BufferedReader(new FileReader (in));
      String word;

      while ((word = fin.readLine()) != null)
      {
        String query = "INSERT INTO stopword(word) VALUES(" + fixApostrophe(word) + ");";
        stmt.execute(query);
      }
    }

    stmt.close();
  }
  catch(Exception e){e.printStackTrace();}
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- write string to file
// ----------------------------------------------------------
private static void writeToFile(String str, String out) throws Exception
{
  FileOutputStream fop = null;
  File file = new File(out);
  fop = new FileOutputStream(file);
  if (!file.exists()) file.createNewFile();
  byte[] contentInBytes = str.getBytes();
  fop.write(contentInBytes);
  fop.flush();
  fop.close();
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- load & preprocess documents
// ----------------------------------------------------------
private static void loadDocuments(String folder) throws Exception
{
  System.out.println("Loading & pre-processing documents from folder " + folder + "...");

  int processed = 0, skipped = 0;
  long startTime, endTime, runTime;
  startTime = System.currentTimeMillis();
  System.out.println("Start time: " + ((startTime % 86400000) / 3600000 + 1) + ":" + (startTime % 3600000) / 60000 + ":" + (startTime % 60000) / 1000);

  Statement stmt  = con.createStatement();
  String query;
  Boolean empty = true;
  
  String urlTechiaith;

  File in = new File(folder);
  if (in.isDirectory())
  {
    // --- POS tag input text (Welsh POS tag set: https://github.com/PorthTechnolegauIaith/postagger/blob/master/doc/README.md)
    File[] file = in.listFiles();
    for (int i = 0; i < file.length; i++)
    {
      empty = false;

      System.out.println("Processing " + file[i].getPath() + "...");

      String doc_id = file[i].getName();
      int extension = doc_id.lastIndexOf('.');
      if (extension > 0) doc_id = doc_id.substring(0, extension);

      // --- read document
      BufferedReader fin = new BufferedReader(new FileReader (file[i]));
      String line;
      String content = "";
      while ((line = fin.readLine()) != null) content += line + "\n";

      // --- separate units from quantity
      content = pretagging(content);

      // --- add document to the database
      query = "INSERT INTO data_document(id, document)\n" +
              "VALUES('" + doc_id + "', " + fixApostrophe(content) + ");";
      System.out.println(query);
      stmt.execute(query);

      // --- split sentences & tokenise them
	  content = useTechiaithService(TechiaithService.POSTAGGER, content);
	  // if no POS tagged content is returned
	  if(content.equals("")) {
		  System.out.println("WARNING: The document " + file[i].getPath() + " could not be processed.  It is either empty or is too long for POS tagging via the Techiaith web service (the maximum URL length permitted by the Techiaith POS tagger is 4094 characters; documents no greater than 3800 characters in length are recommended).");
		  skipped++;
		  continue; // Abandon processing of this document and begin processing the next one (if one exists)
	  }
	  List<String> sentences = Arrays.asList(content.split("(?<=/EOS/-)")); // "/EOS/-" is the end-of-sentence tag used by Techiaith
	  
      int s = 0; // --- sentence number: 1, ... , n

      // --- for each sentence
	  for (String sentence : sentences)
      {
        s++;
        String sentence_id = doc_id + "." + s;

        // --- tag sentence
		String taggedSentenceString = sentence.replaceAll("\\/space/[A-Za-z+-?]*", "").replaceAll("[\\s]+", " ").trim(); // Remove spaces and their tags
		String sentenceString = taggedSentenceString.replaceAll("\\/[A-Za-z+-?]+\\/[A-Za-z+-?]*", "").replaceAll("[\\s]+", " ").trim(); // Remove all tags
		
        System.out.println("Sentence (plain): " + sentenceString);
        System.out.println("Sentence (tagged): " + taggedSentenceString);
		
        // --- add sentence to the database
        query = "INSERT INTO data_sentence(id, doc_id, position, sentence, tagged_sentence)\n" +
                "VALUES('" + sentence_id + "', '" + doc_id + "'," + s + ", " + fixApostrophe(sentenceString) + "," + fixApostrophe(taggedSentenceString) + ");";
        System.out.println(query);
        stmt.execute(query);

        String tags = "";

        // --- separate tagged tokens, e.g.
        // Mae/VBF/- adran/NF/- Gwella/VB/- Iechyd/NM/- o/PREP/- wefan/NMF/TM ...
        String[] parts = taggedSentenceString.split(" ");
		for (int j = 0; j < parts.length; j++)
        {
        // --- separate token from its tag, e.g.
		  
          // token = "chwarae", tag = "VB"
          String part = parts[j];
		  
		  String token = part.substring(0, part.indexOf("/"));
		  String tag = part.substring(part.indexOf("/")+1, part.lastIndexOf("/"));
		  
          // --- generalise tag, e.g. VBF -> V
          String gtag = general(tag);

          // --- lemmatise token, e.g. redais -> rhedeg
		  String lemma = useTechiaithService(TechiaithService.LEMMATIZER, token);
		  if (lemma.equals("")) lemma = token; // if no lemma is found
		  
		  System.out.println(token + "\t" + tag + "\t" + gtag + "\t" + lemma);

          // --- add token to the database
		  query = "INSERT INTO data_token(sentence_id, position, token, lemma, tag, gtag)\n" +
		  "VALUES('" + sentence_id + "', " + (j+1) + ", " + fixApostrophe(token) + ", " + fixApostrophe(lemma) + 
		  ", '" + tag + "', '" + gtag + "');";
          System.out.println(query);
          stmt.execute(query);

          tags += gtag + " ";
        }

        query = "UPDATE data_sentence SET tags = '" + tags + "' WHERE id = '" + sentence_id + "';";
        System.out.println(query);
        stmt.execute(query);

      }
	  processed++;
    }
  }

  query = "UPDATE data_token SET wntag = 'a' WHERE gtag = 'ADJ';"; stmt.execute(query);
  query = "UPDATE data_token SET wntag = 'r' WHERE gtag = 'ADV';"; stmt.execute(query);
  query = "UPDATE data_token SET wntag = 'n' WHERE gtag = 'NN';"; stmt.execute(query);
  query = "UPDATE data_token SET wntag = 'v' WHERE gtag = 'VB';"; stmt.execute(query);

  endTime = System.currentTimeMillis();
  runTime = ((endTime - startTime) / 1000);// 60; // --- run time in minutes
  System.out.println("Document pre-processing done in " + runTime + " sec.\n");
  System.out.println("Documents pre-processed: " + processed);
  System.out.println("Documents skipped: " + skipped);

  stmt.close();

  if (empty)
  {
    System.out.println("WARNING: Input folder empty!");
    System.exit(0);
  }
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- make sure tokens like "3milltir" are split in order to 
//     improve subsequent POS tagging and allow stop words 
//     like "year" to be matched
// ----------------------------------------------------------
private static String pretagging(String txt) {
	
	// Unit prefixes for the Welsh language (including known permissible mutations)
	String[] unit = {"metr",	//"meter"
					"fetr",
					"milltir",	//"mile"
					"filltir",
					"centi",	//"centi"
					"chenti",
					"mili",		//"milli"
					"fili",
					"cilo",		//"kilo"
					"gilo",
					"chilo",
					"gram",		//"gram"
					"eil",		//"sec"
					"mun",		//"min"
					"fun",
					"awr",		//"hour"
					//"hr",		//"awr" is this abbreviated in Welsh?
					"dydd",		//"day"
					"wythnos",	//"week"
					"mis",		//"month"
					"fis",
					"blwyddyn",	//"year"
					"flwyddyn",
					"litr"		//"litre"
					};

	// Source of abbreviations: https://www.yumpu.com/en/document/view/32592101/welsh-abbreviations (from wales.ac.uk)
	String[] abbr = {"m",
					"cm",
					"mm",
					"kg",
					"g",
					"mg",
					"s",
					"h",
					"am",
					"pm",
					"l",
					"ml"};

	int i;
	
	// --- insert white space in front of a unit where necessary
	for (i = 0; i < unit.length; i++)
	txt = txt.replaceAll("[0-9]" + unit[i], "0 " + unit[i]);

	for (i = 0; i < abbr.length; i++)
	txt = txt.replaceAll("[0-9]" + abbr[i] + " ", "0 " + abbr[i] + " ");

	// --- compress multiple punctuation into a single character
	txt = txt.replaceAll("\\!\\!+", "!");
	txt = txt.replaceAll("\\?\\?+", "?");
	
	// --- replace Unicode apostrophes with ASCII apostrophe
	txt = txt.replaceAll("‘", "'");
	txt = txt.replaceAll("’", "'");

	return txt;
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- export results
//  1. output.html  = ranked table with variants grouped together
//  2. output.txt   = dictionary, one entry per line
//  3. output.mixup = MinorThird program that annotates suggested 
//                    terms in text
// ----------------------------------------------------------
private static void export() throws Exception
{
  System.out.println("Exporting results to output.*...");

  Statement stmt  = con.createStatement();
  Statement stmt1 = con.createStatement();
  Statement stmt2 = con.createStatement();
  ResultSet rs, rs1;
  String query;
  DecimalFormat f = new DecimalFormat("0.0000");

  int rank = 0;
  double score = -1;

  // --- initialise outputs
  String output = "<html>"                               + "\n" +
                  "<head>"                               + "\n" +
                  "  <title>FlexiTerm List</title>"      + "\n" +
                  "</head>"                              + "\n" +
                  "<body>"                               + "\n" +
                  "<table border=\"1\">"                 + "\n" +
                  "  <tr>"                               + "\n" +
                  "    <th>Rank</th>"                    + "\n" +
                  "    <th>Term variants</th>"           + "\n" +
                  "    <th>Score</th>"                   + "\n" +
                  "  </tr>"                              + "\n";
  String termlist = "";
  String mixup    = "";
  String csv      = "Rank,Term representative,Score,Frequency";

  query = "SELECT expanded, c, f"                        + "\n" +
          "FROM   term_termhood"                         + "\n" +
          "WHERE  f > " + min                            + "\n" +
          "ORDER BY c DESC;";
  System.out.println(query);
  rs = stmt.executeQuery(query);
  while (rs.next())
  {
    String expanded = rs.getString(1);
    double        c = rs.getDouble(2);
    int   frequency = rs.getInt(3);

    if (c != score) {rank++; score = c;}

    String variants = "";
    String representative = "";

    // --- find all term variants
    query = "SELECT LOWER(P.phrase), COUNT(*)"                 + "\n" +
            "FROM   term_normalised N, term_phrase P"          + "\n" +
            "WHERE  N.expanded = " + fixApostrophe(expanded)   + "\n" +
            "AND    N.normalised = P.normalised"               + "\n" +
            "GROUP BY LOWER(P.phrase)"                         + "\n" +
            "ORDER BY COUNT(*) DESC, LOWER(P.phrase);";
    System.out.println(query);
    rs1 = stmt1.executeQuery(query);
    while (rs1.next())
    {
      String variant = rs1.getString(1);

      if (representative.equals(""))
      {
        representative = variant;
        query = "UPDATE term_termhood SET representative = " + fixApostrophe(representative) + " WHERE expanded = " + fixApostrophe(expanded) + ";";
        System.out.println(query);
        stmt2.execute(query);

        csv += "\n" + rank + ",\"" + representative + "\"," + f.format(c) + "," + frequency;
      }

      termlist += variant + "\n";

      variants += "      " + variant + "<br/>\n";

      variant = mixupTokens(variant);

      String line = "";
      String[] tokens = variant.split(" ");
      for (int i = 0; i < tokens.length; i++)
      {
        String token = tokens[i];
        line += "eqi('" + token.replaceAll("'", "\\\\'") + "') ";
      }
      line = "||\n... [ " + line + "] ... ";
      mixup += line;
    }
    rs1.close();

    output += "  <tr>"                                                               + "\n" +
              "    <td align = \"right\" valign=\"top\">" + rank + "</td>"           + "\n" +
              "    <td align = \"left\">"                                            + "\n" +
                     variants                                                        +
              "    </td>"                                                            + "\n" +
              "    <td align = \"right\" valign=\"top\">" + f.format(c) + "</td>"    + "\n" +
              "  </tr>"                                                              + "\n";
  }
  rs.close();

  output += "</table>" + "\n" +
            "</body>"  + "\n" +
            "</html>"  + "\n";

  if (mixup.length() > 2)
  {
    mixup = "defSpanType term =: " + mixup.substring(2) + ";\n";
    mixup += "defSpanType token =term: ... [ any ] ... ;";
  }
 
  writeToFile(output,   "./output.html");
  writeToFile(termlist, "./output.txt");
  writeToFile(mixup,    "./output.mixup");
  writeToFile(csv,      "./output.csv");

  stmt.close();
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- separate tokens as they are understood in mixup
// ----------------------------------------------------------
private static String mixupTokens(String txt)
{
  // --- separate hyphen, apostrophe and slash
  txt = txt.replaceAll("\\-", " - ");
  txt = txt.replaceAll("\\.", " . ");
  txt = txt.replaceAll("'", " ' ");
  txt = txt.replaceAll("/", " / ");

  // --- separate digits from other characters
  char after = ' ';
  for (int i = txt.length() - 1; i >= 0; i--)
  {
    char before = txt.charAt(i);

    if (!Character.isWhitespace(before) && !Character.isWhitespace(after))
    {
      if (Character.isDigit(after))
      {
        // --- K9 -> K 9
        if (!Character.isDigit(before)) txt = txt.substring(0, i+1) + " " + txt.substring(i+1);
      }
      else // --- if (!Character.isDigit(after))
      {
        // --- 4square -> 4 square
        if (Character.isDigit(before))  txt = txt.substring(0, i+1) + " " + txt.substring(i+1);
      }
    }

    after = before;
  }

  // --- remove extra white spaces
  while (txt.length() > (txt.replaceAll("  ", " ")).length()) txt = txt.replaceAll("  ", " ");

  return txt;
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- construct url for contacting appropriate web service
// ----------------------------------------------------------
private static String useTechiaithService(TechiaithService service, String text)
{
	StringBuilder urlSB = null;
	
	try {
		switch (service) {
			case POSTAGGER:
				urlSB = new StringBuilder(apiPOSTaggerAddress);
				urlSB.append("api_key=".concat(apiPOSTaggerKey));
				urlSB.append("&text=".concat(URLEncoder.encode(text.replaceAll("[\\t\\n\\r]+", " ").trim(), "UTF-8")));  // replace all tab, new line, and carriage return characters with a single space
				break;
			case LEMMATIZER:
				urlSB = new StringBuilder(apiLemmatizerAddress);
				urlSB.append("api_key=".concat(apiLemmatizerKey));
				urlSB.append("&text=".concat(URLEncoder.encode(text.toLowerCase(), "UTF-8")));
				break;
			case SPELLCHECKER:
				urlSB = new StringBuilder(apiCysillOnlineAddress);
				urlSB.append("api_key=".concat(apiCysillOnlineKey));
				urlSB.append("&text=".concat(URLEncoder.encode(text, "UTF-8")));
				urlSB.append("&max_errors=".concat(String.valueOf(max)));
				break;
			default:
				System.out.println("buildUrl() error: invalid service specified.");
		}
	}
	catch(UnsupportedEncodingException e) {
		System.out.println("useTechiaithService() URL encoding error: " + e.toString());
	}
	catch(Exception e) {
		System.out.println("useTechiaithService() error: " + e.toString());
	}
	return connectToTechiaithURL(urlSB.toString());
}
// ----------------------------------------------------------


// ----------------------------------------------------------
// --- connect to a url and obtain response
// ----------------------------------------------------------
private static String connectToTechiaithURL(String urlString)
{
	String responseAsString = "";
	
	try {
		URL url = new URL(urlString);
		System.out.println(url.toString());
		HttpsURLConnection connection = (HttpsURLConnection) url.openConnection();
		connection.connect();
		
		if (connection.getResponseCode() == 200) {
			JSONObject responseObject = new JSONObject(new JSONTokener(connection.getInputStream()));
			responseAsString = responseObject.optString("result");
		}
		else {
			System.out.println("Hmm, connection refused with response: [" + connection.getResponseCode() + "] " + connection.getResponseMessage());
		}

		connection.disconnect();
	}
	catch(JSONException e) {
		System.out.println("connectToURL() JSON error: " + e.getMessage());
	}
	catch(Exception e) {
		System.out.println("connectToURL() error: " + e.getMessage());
	}
	return responseAsString;
}
// ----------------------------------------------------------
}
