# Prolog_Abschlussprojekt

## Umfang
Es wurden allen Teilaufgaben der ersten Aufgabe bearbeitet.

Die Verbessungen durch Strength Reduction und Constant Folding werden ausgegeben und außerdem
sofort in einen neuen AST eingebaut.
Das verbesserte Programm wird mit der Endung .bapl abgespeichert, sodass zukünftige Durchläufe
des Programms von den Verbesserungen ohne erneutes Durchführen profitieren können.
Die .bapl Datei muss jedoch manuell auf dem neusten Stand gehalten werden, das Programm erkennt nicht,
ob die .apl- und .bapl-Version denselben Stand wiederspiegeln. Auch wird nicht automatisch 
die .bapl-Datei ausgewählt.

Bei der Strength Reduction wurde zu Gunsten von Constant Folding auf das Reduzieren von beispielsweise 15*x 
zu x << 4 - x verzichtet, da bei Shift einige Faltungsmöglichkeiten verloren gehen, wenn die Vorzeichen rechts
nicht bekannt sind.

Das Erkennen von Endlosschleifen und das Eliminieren von totem Code wurden in den abstrakten Interpreter
eingebaut.

## Struktur
Das Projekt besteht aus acht Prolor Source Files
* load.pl
    * Zum Laden der Source Files. 
* imp_int.pl
    * Zum imperativen Interpretieren eines .apl-Files
* abs_int.pl
    * Zum abstrakten Interpretieren eines .apl-Files
* parser.pl
    * Zum Parser der .apl-Datei
* fileProcessor.pl
    * Ein Wrapper für das Parser, der Optimierung und Ausgabe hinzuschaltet.
* logger.pl
    * Zur einheitlichen Ausgabe von Infos, Warnungen und Fehlern
* strength_reduction.pl
    * Strength Reduction auf dem AST
* constant_folding.pl
    * Constant Folding auf dem AST
    
und einer Domäne (erweiterbar)
* null_pos_neg.pl

## Bedienung
Es muss das Modul load.pl geladen werden. 

Anschließend kann man folgende Prädikate aufrufen:
* abs_int(+Filename,-State,?Options): abstraktes Interpretieren
* imp_int(+Filename,?Options): imperatives Interpretieren
* getOptions(-Options): Gibt eine Übersicht über die Optionen
* set_loglevel(+Loglevel): Setzt das Loglevel. info, warning, error, nothing
* loglevel(+Loglevel): aktuelle Loglevel

Der Filename muss dabei als String ("") angegeben werden.