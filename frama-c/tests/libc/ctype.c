/* run.config
   STDOPT: #"-eva-slevel 4"
*/
#include <stdio.h>
#include <ctype.h>

int main() {
  int r;
    r = isascii(EOF);
    //@ assert r == 0;
    r = isascii(0);
    //@ assert r != 0;
    r = isascii(1);
    //@ assert r != 0;
    r = isascii(32);
    //@ assert r != 0;
    r = isascii(48);
    //@ assert r != 0;
    r = isascii(65);
    //@ assert r != 0;
    r = isascii(122);
    //@ assert r != 0;
    r = isalnum(EOF);
    //@ assert r == 0;
    r = isalnum(0);
    //@ assert r == 0;
    r = isalnum(1);
    //@ assert r == 0;
    r = isalnum(32);
    //@ assert r == 0;
    r = isalnum(48);
    //@ assert r != 0;
    r = isalnum(65);
    //@ assert r != 0;
    r = isalnum(122);
    //@ assert r != 0;
    r = isalpha(EOF);
    //@ assert r == 0;
    r = isalpha(0);
    //@ assert r == 0;
    r = isalpha(1);
    //@ assert r == 0;
    r = isalpha(32);
    //@ assert r == 0;
    r = isalpha(48);
    //@ assert r == 0;
    r = isalpha(65);
    //@ assert r != 0;
    r = isalpha(122);
    //@ assert r != 0;
    r = isascii(EOF);
    //@ assert r == 0;
    r = isascii(0);
    //@ assert r != 0;
    r = isascii(1);
    //@ assert r != 0;
    r = isascii(32);
    //@ assert r != 0;
    r = isascii(48);
    //@ assert r != 0;
    r = isascii(65);
    //@ assert r != 0;
    r = isascii(122);
    //@ assert r != 0;
    r = isascii(255);
    //@ assert r == 0;
    r = isblank(EOF);
    //@ assert r == 0;
    r = isblank(0);
    //@ assert r == 0;
    r = isblank(1);
    //@ assert r == 0;
    r = isblank(32);
    //@ assert r != 0;
    r = isblank(48);
    //@ assert r == 0;
    r = isblank(65);
    //@ assert r == 0;
    r = isblank(122);
    //@ assert r == 0;
    r = iscntrl(EOF);
    //@ assert r == 0;
    r = iscntrl(0);
    //@ assert r != 0;
    r = iscntrl(1);
    //@ assert r != 0;
    r = iscntrl(32);
    //@ assert r == 0;
    r = iscntrl(48);
    //@ assert r == 0;
    r = iscntrl(65);
    //@ assert r == 0;
    r = iscntrl(122);
    //@ assert r == 0;
    r = isdigit(EOF);
    //@ assert r == 0;
    r = isdigit(0);
    //@ assert r == 0;
    r = isdigit(1);
    //@ assert r == 0;
    r = isdigit(32);
    //@ assert r == 0;
    r = isdigit(48);
    //@ assert r != 0;
    r = isdigit(65);
    //@ assert r == 0;
    r = isdigit(122);
    //@ assert r == 0;
    r = isdigit(255);
    //@ assert r == 0;
    r = isgraph(EOF);
    //@ assert r == 0;
    r = isgraph(0);
    //@ assert r == 0;
    r = isgraph(1);
    //@ assert r == 0;
    r = isgraph(32);
    //@ assert r == 0;
    r = isgraph(48);
    //@ assert r != 0;
    r = isgraph(65);
    //@ assert r != 0;
    r = isgraph(122);
    //@ assert r != 0;
    r = islower(EOF);
    //@ assert r == 0;
    r = islower(0);
    //@ assert r == 0;
    r = islower(1);
    //@ assert r == 0;
    r = islower(32);
    //@ assert r == 0;
    r = islower(48);
    //@ assert r == 0;
    r = islower(65);
    //@ assert r == 0;
    r = islower(122);
    //@ assert r != 0;
    r = isprint(EOF);
    //@ assert r == 0;
    r = isprint(0);
    //@ assert r == 0;
    r = isprint(1);
    //@ assert r == 0;
    r = isprint(32);
    //@ assert r != 0;
    r = isprint(48);
    //@ assert r != 0;
    r = isprint(65);
    //@ assert r != 0;
    r = isprint(122);
    //@ assert r != 0;
    r = ispunct(EOF);
    //@ assert r == 0;
    r = ispunct(0);
    //@ assert r == 0;
    r = ispunct(1);
    //@ assert r == 0;
    r = ispunct(32);
    //@ assert r == 0;
    r = ispunct(48);
    //@ assert r == 0;
    r = ispunct(65);
    //@ assert r == 0;
    r = ispunct(122);
    //@ assert r == 0;
    r = isspace(EOF);
    //@ assert r == 0;
    r = isspace(0);
    //@ assert r == 0;
    r = isspace(1);
    //@ assert r == 0;
    r = isspace(32);
    //@ assert r != 0;
    r = isspace(48);
    //@ assert r == 0;
    r = isspace(65);
    //@ assert r == 0;
    r = isspace(122);
    //@ assert r == 0;
    r = isupper(EOF);
    //@ assert r == 0;
    r = isupper(0);
    //@ assert r == 0;
    r = isupper(1);
    //@ assert r == 0;
    r = isupper(32);
    //@ assert r == 0;
    r = isupper(48);
    //@ assert r == 0;
    r = isupper(65);
    //@ assert r != 0;
    r = isupper(122);
    //@ assert r == 0;
    r = isxdigit(EOF);
    //@ assert r == 0;
    r = isxdigit(0);
    //@ assert r == 0;
    r = isxdigit(1);
    //@ assert r == 0;
    r = isxdigit(32);
    //@ assert r == 0;
    r = isxdigit(48);
    //@ assert r != 0;
    r = isxdigit(65);
    //@ assert r != 0;
    r = isxdigit(122);
    //@ assert r == 0;
    r = isxdigit(255);
    //@ assert r == 0;
    r = tolower(EOF);
    //@ assert r == EOF;
    r = tolower(0);
    //@ assert r == 0;
    r = tolower(1);
    //@ assert r == 1;
    r = tolower(32);
    //@ assert r == 32;
    r = tolower(48);
    //@ assert r == 48;
    r = tolower(65);
    //@ assert r == 97;
    r = tolower(122);
    //@ assert r == 122;
    r = toupper(EOF);
    //@ assert r == EOF;
    r = toupper(0);
    //@ assert r == 0;
    r = toupper(1);
    //@ assert r == 1;
    r = toupper(32);
    //@ assert r == 32;
    r = toupper(48);
    //@ assert r == 48;
    r = toupper(65);
    //@ assert r == 65;
    r = toupper(122);
    //@ assert r == 90;
}