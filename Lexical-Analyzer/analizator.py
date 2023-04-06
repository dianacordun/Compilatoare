import colorama
import re
from colorama import Fore

# operatori recunoscuti in Python
operatori = ["+", "-", "*", "**", "/", "//", "%", "<<", ">>", "!", "&", "|", "^", "~", "<", ">", "<=", ">=", "==",
             "!=", "<>", "+=", "-=", "*=", "/=", "//=", "%=", "**=", "&=", "|=", "^=", ">>=", "<<="]

# simboluri speciale ', ", \, @
simboluri_speciale = ["\'", "\"", "\\", "@"]

# delimitatorii pentru expresii, liste, dictionare etc.
delimitatori = [".", ";", ":", ",", "(", ")", "[", "]", "{", "}", '`', "="]

# cuvinte rezervate
cuvinte_cheie = ['and', 'as', 'assert', 'break', 'class', 'def', 'del', 'elif', 'else', 'except', 'exec',
                 'finally', 'for', 'from', 'global', 'if', 'import', 'in', 'is', 'lambda', 'not', 'or',
                 'pass', 'print', 'raise', 'return', 'try', 'while', 'with', 'yield', 'True', 'False']

identificatori = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r",
                  "s", "t", "u", "v", "w", "x", "z", "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K",
                  "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z", "1", "2", "3",
                  "4", "5", "6", "7", "8", "9", "0", "_"]


def este_operator(x):
    if x in operatori:
        return True
    return False


def este_delimitator(x):
    if x in delimitatori:
        return True
    return False


def este_simbol_special(x):
    if x in simboluri_speciale:
        return True
    return False


def este_cuvant_cheie(x):
    if x in cuvinte_cheie:
        return True
    return False


def este_identificator(identificator):
    try:
        identificator.index('"') and identificator.index("'") and int(identificator[0])
        # nu poate sa inceapa cu un numar sau sa aiba ghilimele inauntru, Lexical error altfel
        return False
    except ValueError:
        pass
    if all(element in identificatori for element in identificator):
        return True
    return False


def analizator_lexical(linii_fisier):
    continut_fisier = "".join(linii_fisier)
    pointer = 0
    linie = 1

    while pointer < len(continut_fisier):  # pana nu ajung la finalul sirului
        # sunt ignorate spatiile, liniile noi, tab-urile
        if continut_fisier[pointer] in ['\n', '\t', ' ']:
            if continut_fisier[pointer] == '\n':
                linie += 1
            pointer += 1
            continue
        elif continut_fisier[pointer] == '#':  # CAZ COMENTARIU
            pointer_comm = pointer + 1  # pointer = începutul comentariului
            comm = ''
            while pointer_comm < len(continut_fisier):
                if continut_fisier[pointer_comm] == '\n':
                    break
                else:
                    comm += continut_fisier[pointer_comm]
                    pointer_comm += 1

            print(f'"#{comm}" : COMENTARIU, LUNGIME: {len(comm)}, LINIE: {linie}, POINTER: {pointer}')
            if continut_fisier[pointer_comm] == '\n':
                linie += 1
            pointer = pointer_comm + 1

        elif continut_fisier[pointer] == '"':  # CAZ SIR 1
            pointer_string = pointer + 1  # inceputul string-ului este pointer
            string = ''
            closed = False
            multiline_string = False
            while pointer_string < len(continut_fisier):
                if continut_fisier[pointer_string] == '\n':
                    linie += 1
                if continut_fisier[pointer_string] != '"':
                    string += continut_fisier[pointer_string]
                    pointer_string += 1
                else:
                    # verific sa nu fie multi-line string
                    if multiline_string and pointer_string != len(continut_fisier) - 2:  # inchidem sirul
                        if continut_fisier[pointer_string + 1] == '"' and continut_fisier[pointer_string + 2] == '"':
                            closed = True
                            pointer_string += 2
                            break
                    elif pointer_string == pointer + 1 and pointer_string != len(continut_fisier) - 1 and \
                            continut_fisier[
                                pointer_string + 1] == '"':  # nu sunt pe ultima pozitie si abia am deschis sirul
                        multiline_string = True
                        pointer_string += 2
                    elif not multiline_string:
                        closed = True
                        break
            if pointer_string > len(continut_fisier):
                print(Fore.RED + "Eroare Lexicala: Sir neîncheiat!")
                quit(0)
            if not closed or (continut_fisier[pointer_string] == "\n" and pointer_string + 1 > len(fisier)):
                print(Fore.RED + "Eroare Lexicala: Sir neîncheiat!")
            elif multiline_string:
                print(f'"""{string}""" : SIR MULTILINE, LUNGIME: {len(string)}, LINIE: {linie}, POINTER: {pointer}')
            else:
                print(f'"{string}" : SIR, LUNGIME: {len(string)}, LINIE: {linie}, POINTER: {pointer}')
            pointer = pointer_string + 1
        elif continut_fisier[pointer] == "'":  # CAZ SIR 2
            pointer_string = pointer + 1  # începutul string-ului este pointer
            string = ''
            closed = False
            multiline_string = False
            while pointer_string < len(continut_fisier):
                if continut_fisier[pointer_string] == '\n':
                    linie += 1
                if continut_fisier[pointer_string] != "'":
                    string += continut_fisier[pointer_string]
                    pointer_string += 1
                else:
                    # verific sa nu fie multi-line string
                    if multiline_string and pointer_string != len(continut_fisier) - 2:  # inchidem sirul
                        if continut_fisier[pointer_string + 1] == "'" and continut_fisier[pointer_string + 2] == "'":
                            closed = True
                            pointer_string += 2
                            break
                    elif pointer_string == pointer + 1 and pointer_string != len(continut_fisier) - 1 and \
                            continut_fisier[
                                pointer_string + 1] == "'":  # nu sunt pe ultima pozitie si abia am deschis sirul
                        multiline_string = True
                        pointer_string += 2
                    elif not multiline_string:
                        closed = True
                        break
            if not closed:
                print(Fore.RED + "Eroare Lexicala: Sir neîncheiat!")
            elif multiline_string:
                print(f"'''{string}''' : SIR MULTILINE, LUNGIME: {len(string)}, LINIE: {linie}, POINTER: {pointer}")
            else:
                print(f"'{string}' : SIR, LUNGIME: {len(string)}, LINIE: {linie}, POINTER: {pointer}")
            pointer = pointer_string + 1
        else:
            pointer_token = pointer  # pointer = inceputul token-ului
            token = ''
            while pointer_token < len(
                    continut_fisier):  # ex '89', pt = 3, pt la final = 5 care e spatiu, deci de la 6 incep next
                if continut_fisier[pointer_token] in ['\n', '\t', ' ']:
                    break
                elif continut_fisier[pointer_token] == '"' or continut_fisier[pointer_token] == "'" or continut_fisier[pointer_token] == '#' :
                    break
                else:
                    token += continut_fisier[pointer_token]
                    pointer_token += 1

            # verific daca token-ul curent este float
            if re.match(r"([+-]?[0-9]*\.[0-9]*)", token):
                print(f'{token} : FLOAT, LUNGIME: {len(token)}, LINIE: {linie}, POINTER: {pointer}')
                pointer = pointer_token + 1
                continue

            tokeni_separati = re.findall(r"\w+|[^\s\w]|[-:\w]",
                                         token)  # ex variabila: contine 2 tokeni care trb separati

            # de aici trebuie aflat tipul lor, mom tratez doar cazul unui singur token
            # TOKEN:  TIP_TOKEN, LUNGIME_TOKEN, LINIE_TOKEN, POINTER_START, (opt) MES_EROARE
            for token in tokeni_separati:

                if re.match(r"^[0-9]*$", token):
                    print(f'{token} : INTEGER, LUNGIME: {len(token)}, LINIE: {linie}, POINTER: {pointer}')
                elif este_delimitator(token):
                    print(f'{token} : DELIMITATOR, LUNGIME: {len(token)}, LINIE: {linie}, POINTER: {pointer}')
                elif este_simbol_special(token):
                    print(f'{token} : SIMBOL SPECIAL, LUNGIME: {len(token)}, LINIE: {linie}, POINTER: {pointer}')
                elif este_cuvant_cheie(token):
                    print(f'{token} : CUVANT CHEIE, LUNGIME: {len(token)}, LINIE: {linie}, POINTER: {pointer}')
                elif este_operator(token):
                    print(f'{token} : OPERATOR, LUNGIME: {len(token)}, LINIE: {linie}, POINTER: {pointer}')
                elif este_identificator(token):
                    print(f'{token} : IDENTIFICATOR, LUNGIME: {len(token)}, LINIE: {linie}, POINTER: {pointer}')
                else:
                    print(f'{token} : SIMBOL NERECUNOSCUT, LUNGIME: {len(token)}, LINIE: {linie}, POINTER: {pointer})')
                    print(Fore.RED + "Eroare Lexicala: Caracter ilegal!")

                pointer += len(token)

            if continut_fisier[pointer_token] == '\n':
                linie += 1

            if continut_fisier[pointer_token] == '"' or continut_fisier[pointer_token] == "'":
                pointer = pointer_token
            else:
                pointer = pointer_token + 1


if __name__ == '__main__':
    colorama.init(autoreset=True)
    nume_fisier = input("Introduceti numele fisierului: ")

    try:
        fisier = open(nume_fisier, 'r')
    except:
        print(Fore.RED + "Numele fisierului este gresit.")
        quit(0)

    linii = fisier.readlines()
    if len(linii) <= 0:
        print(Fore.RED + "Fisierul este gol.")
        quit(0)

    print(Fore.BLUE + 'TOKEN: TIP_TOKEN, LUNGIME_TOKEN, LINIE_TOKEN, POINTER_START, (opt) MESAJ_EROARE')

    analizator_lexical(linii)

    print(Fore.BLUE + "FINAL FISIER")
