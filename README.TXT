Java requirements:

java version "1.6.0"
Java(TM) SE Runtime Environment (build 1.6.0-b105)
Java HotSpot(TM) Client VM (build 1.6.0-b105, mixed mode)

To run FlexiTermCymraeg:

1. Place plain text files into a folder named "text".
2. OPTIONAL: Replace file stoplist.txt with your own if needed.
3. Run FlexiTermCymraeg.bat from the command line.
4. Check results by double-clicking output.html

Folders:

lib              : External Java libraries needed to run FlexiTerm.
text             : Input text files.

Files:

FlexiTermCymraeg.bat    : Batch file that runs FlexiTermCymraeg.java.
flexitermcymraeg.sqlite : An sqlite database used by FlexiTermCymraeg.java.
output.csv       		: A table of results: Rank | Term variants | Score | Frequency
output.html      		: A table of results: Rank | Term variants | Score
output.txt       		: A list of recognised term variants ordered by their scores.
output.mixup     		: A Mixup file used by MinorThird to annotate term occurrences in text.
output.bat       		: Batch file used to run output.mixup against the files in the text folder. (Windows)
output.sh        		: Shell script used to run output.mixup against the files in the text folder. (Unix)
settings.txt     		: Specifies 1) term pattern(s), 2) stoplist, 3) maximum number of spell check corrections per token 4) minimum term candidate frequency.
stoplist.txt     		: Stoplist used to filter out stopwords.
tmp.txt          		: Listing output used for debugging.

Java classes:

FlexiTermCymraeg.java   : Main Java class.

Default settings:

pattern = "(((NN (JJ )*)IN NN( JJ)*)|(((NN|JJ) )+(NN|JJ)))"
stoplist = ".\\stoplist.txt"										: stoplist location - modify the file content if necessary
max = 3																: number of suggestions to seek via spellchecker - reduce for better similarity
min = 2																: term frequency threshold: occurrence > min - increase for better precision
apiPOSTaggerAddress = "https://api.techiaith.org/pos/v1/?"			: Techiaith POS Tagger API URL
apiPOSTaggerKey = "485fb2e4-1536-4afc-a0e3-65ca28faf398"			: Techiaith POS Tagger API key
apiLemmatizerAddress = "https://api.techiaith.org/lemmatizer/v1/?"	: Techiaith Lemmatizer API URL
apiLemmatizerKey = "fa3cf0ac-5d9f-4ce9-ae0d-cae9db2ad28d"			: Techiaith Lemmatizer API key
apiCysillOnlineAddress = "https://api.techiaith.org/cysill/v1/?"	: Techiaith CysillOnline (spellchecker) API URL
apiCysillOnlineKey = "c358ccd2-68f2-464f-a37a-b8a0249aac11"			: Techiaith CysillOnline (spellchecker) API key