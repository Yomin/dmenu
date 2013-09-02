/* See LICENSE file for copyright and license details. */
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#include <sys/queue.h>
#include <sys/stat.h>
#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>
#ifdef XINERAMA
#include <X11/extensions/Xinerama.h>
#endif
#include "draw.h"

#define INTERSECT(x,y,w,h,r) (MAX(0, MIN((x)+(w),(r).x_org+(r).width)  - MAX((x),(r).x_org)) \
							* MAX(0, MIN((y)+(h),(r).y_org+(r).height) - MAX((y),(r).y_org)))
#define MIN(a,b) ((a) < (b) ? (a) : (b))
#define MAX(a,b) ((a) > (b) ? (a) : (b))

#ifndef PATH_MAX
#define PATH_MAX 256
#endif

#define DIR_NODIR 0
#define DIR_ISDIR 1
#define DIR_LAST  2

typedef struct Item Item;
struct Item {
	char *text;
	Item *left, *right;
};

typedef struct Elem Elem;
struct Elem {
	CIRCLEQ_ENTRY(Elem) chain;
	char text[BUFSIZ], path[PATH_MAX];
	int width, maxwidth;
	char dir;
};
typedef struct ElemList ElemList;
CIRCLEQ_HEAD(ElemList, Elem);

static void appenditem(Item *item, Item **list, Item **last);
static void calcoffsets(void);
static char *cistrstr(const char *s, const char *sub);
static void drawmenu(void);
static void grabkeyboard(void);
static void insert(const char *str, ssize_t n, Bool domatch);
static void keypress(XKeyEvent *ev);
static void match(void);
static size_t nextrune(int inc);
static void paste(void);
static void readstdin(void);
static int listdir(void);
static void run(void);
static void setup(void);
static void usage(void);

static ElemList elemlist;
static Elem *elem;
static char pwd[PATH_MAX], cwd[PATH_MAX] = "";
static int bh, mw, mh;
static int promptw, inputw;
static int fsize = 0, cwdlen = 0;
static Bool exactmatch;
static size_t cursor = 0;
static const char *font = NULL;
static const char *prompt = NULL;
static const char *normbgcolor = "#222222";
static const char *normfgcolor = "#bbbbbb";
static const char *selbgcolor  = "#005577";
static const char *selfgcolor  = "#eeeeee";
static unsigned int lines = 0;
static unsigned long normcol[ColLast];
static unsigned long selcol[ColLast];
static Atom clip, utf8;
static Bool topbar = True, filecompletion = False;
static DC *dc;
static Item *items = NULL, *fitems = NULL;
static Item *matches, *matchend;
static Item *prev, *curr, *next, *sel, *tabsel = NULL;
static Window win;
static XIC xic;

static int (*fstrncmp)(const char *, const char *, size_t) = strncmp;
static char *(*fstrstr)(const char *, const char *) = strstr;

int
main(int argc, char *argv[]) {
	Bool fast = False;
	int i;

	for(i = 1; i < argc; i++)
		/* these options take no arguments */
		if(!strcmp(argv[i], "-v")) {      /* prints version information */
			puts("dmenu-"VERSION", © 2006-2012 dmenu engineers, 2013 yomin, see LICENSE for details");
			exit(EXIT_SUCCESS);
		}
		else if(!strcmp(argv[i], "-b"))   /* appears at the bottom of the screen */
			topbar = False;
		else if(!strcmp(argv[i], "-f"))   /* grabs keyboard before reading stdin */
			fast = True;
		else if(!strcmp(argv[i], "-i")) { /* case-insensitive item matching */
			fstrncmp = strncasecmp;
			fstrstr = cistrstr;
		}
		else if(!strcmp(argv[i], "-fc"))  /* file completion */
			filecompletion = True;
		else if(i+1 == argc)
			usage();
		/* these options take one argument */
		else if(!strcmp(argv[i], "-l"))   /* number of lines in vertical list */
			lines = atoi(argv[++i]);
		else if(!strcmp(argv[i], "-p"))   /* adds prompt to left of input field */
			prompt = argv[++i];
		else if(!strcmp(argv[i], "-fn"))  /* font or font set */
			font = argv[++i];
		else if(!strcmp(argv[i], "-nb"))  /* normal background color */
			normbgcolor = argv[++i];
		else if(!strcmp(argv[i], "-nf"))  /* normal foreground color */
			normfgcolor = argv[++i];
		else if(!strcmp(argv[i], "-sb"))  /* selected background color */
			selbgcolor = argv[++i];
		else if(!strcmp(argv[i], "-sf"))  /* selected foreground color */
			selfgcolor = argv[++i];
		else
			usage();

	dc = initdc();
	initfont(dc, font);

	if(fast) {
		grabkeyboard();
		readstdin();
	}
	else {
		readstdin();
		grabkeyboard();
	}
	setup();
	run();

	return 1; /* unreachable */
}

void cleanup(int status) {
	if(items)
		free(items);
	if(fitems)
		free(fitems);
	while(elemlist.cqh_first != (void*)&elemlist) {
	    elem = elemlist.cqh_first;
		CIRCLEQ_REMOVE(&elemlist, elem, chain);
		free(elem);
	}
	exit(status);
}

void
appenditem(Item *item, Item **list, Item **last) {
	if(*last)
		(*last)->right = item;
	else
		*list = item;

	item->left = *last;
	item->right = NULL;
	*last = item;
}

void
calcoffsets(void) {
	int i, n;

	if(lines > 0)
		n = lines * bh;
	else
		n = mw - (promptw + inputw + textw(dc, "<") + textw(dc, ">"));
	/* calculate which items will begin the next page and previous page */
	for(i = 0, next = curr; next; next = next->right)
		if((i += (lines > 0) ? bh : MIN(textw(dc, next->text), n)) > n)
			break;
	for(i = 0, prev = curr; prev && prev->left; prev = prev->left)
		if((i += (lines > 0) ? bh : MIN(textw(dc, prev->left->text), n)) > n)
			break;
}

char *
cistrstr(const char *s, const char *sub) {
	size_t len;

	for(len = strlen(sub); *s; s++)
		if(!strncasecmp(s, sub, len))
			return (char *)s;
	return NULL;
}

void
drawmenu(void) {
	int curpos;
	Item *item;
	Elem *e;

	dc->x = 0;
	dc->y = 0;
	dc->h = bh;
	drawrect(dc, 0, 0, mw, mh, True, BG(dc, normcol));

	if(prompt) {
		dc->w = promptw;
		drawtext(dc, prompt, True, selcol);
		dc->x = dc->w;
	}

	/* draw finished front input elems */
	e = elemlist.cqh_first;
	while(e && e != elem) {
		dc->w = e->width;
		drawtext(dc, e->text, False, normcol);
		dc->x += dc->w;
		if(e->dir == DIR_ISDIR)
			dc->x -= 8;
		e = e->chain.cqe_next;
	}

	/* draw input field */
    if(elem->chain.cqe_next == (void*)&elemlist)
        dc->w = lines > 0 || !matches ? mw - dc->x : elem->maxwidth;
    else
        dc->w = elem->width;
	if((curpos = textnw(dc, elem->text, cursor)) < dc->w)
		drawrect(dc, curpos+6, 0, 6, dc->h, True, BG(dc, selcol));
	drawtext(dc, elem->text, False, normcol);
	dc->x += dc->w;

	/* draw finished rear input elems */
	e = elem->chain.cqe_next;
	while(e != (void*)&elemlist) {
		dc->w = e->width;
		drawtext(dc, e->text, False, normcol);
		dc->x += dc->w;
        if(e->dir == DIR_ISDIR)
			dc->x -= 8;
		e = e->chain.cqe_next;
	}

	if(elem->chain.cqe_next != (void*)&elemlist)
		dc->x += (lines > 0 || !matches) ? 0 : elem->maxwidth-elem->width;

	if(lines > 0) {
		/* draw vertical list */
		dc->w = mw - dc->x;
		for(item = curr; item != next; item = item->right) {
			dc->y += dc->h;
			drawtext(dc, item->text, True, (item == sel) ? selcol : normcol);
		}
	}
	else if(matches) {
		/* draw horizontal list */
		dc->w = textw(dc, "<");
		if(curr->left)
			drawtext(dc, "<", True, normcol);
		for(item = curr; item != next; item = item->right) {
			dc->x += dc->w;
			dc->w = MIN(textw(dc, item->text), mw - dc->x - textw(dc, ">"));
			drawtext(dc, item->text, True, (item == sel) ? selcol : normcol);
		}
		dc->w = textw(dc, ">");
		dc->x = mw - dc->w;
		if(next)
			drawtext(dc, ">", True, normcol);
	}
	mapdc(dc, win, mw, mh);
}

void
grabkeyboard(void) {
	int i;

	/* try to grab keyboard, we may have to wait for another process to ungrab */
	for(i = 0; i < 1000; i++) {
		if(XGrabKeyboard(dc->dpy, DefaultRootWindow(dc->dpy), True,
				GrabModeSync, GrabModeAsync, CurrentTime) == GrabSuccess)
			return;
		usleep(1000);
	}
	eprintf("cannot grab keyboard\n");
}

void
insert(const char *str, ssize_t n, Bool domatch) {
	if(strlen(elem->text) + n > BUFSIZ - 1)
		return;
	/* move existing text out of the way, insert new text, and update cursor */
	memmove(&elem->text[cursor + n], &elem->text[cursor], BUFSIZ - cursor - MAX(n, 0));
	if(n > 0)
		memcpy(&elem->text[cursor], str, n);
	cursor += n;
	if(domatch) {
		elem->width = textw(dc, elem->text) -6;
		match();
	}
}

int
pfxcmp(const char *pfx, const char *str, int plen) {
	int len = 0;
	while(*pfx && *str && len < plen && *pfx == *str) {
		len++;
		pfx++;
		str++;
	}
	return !len ? plen : len;
}

Bool isdir(const char *path, const char *name) {
	char buf[PATH_MAX];
	struct stat sbuf;
	sprintf(buf, "%s%s", path, name);
	if(stat(buf, &sbuf) == -1)
		return False;
	return S_ISDIR(sbuf.st_mode);
}

void
newelem() {
	tabsel = NULL;

	strcpy(elem->text, sel->text);
	if(elem != elemlist.cqh_first && isdir(elem->path, elem->text)) {
		elem->dir = DIR_ISDIR;
		strcpy(elem->text+strlen(elem->text), "/");
		if(*cwd) {
			strcpy(cwd+cwdlen, elem->text);
			cwdlen += strlen(elem->text);
		}
		else {
			strcpy(cwd, elem->path);
			cwdlen = strlen(elem->path);
			strcpy(cwd+cwdlen, elem->text);
			cwdlen += strlen(elem->text);
		}
	}
	else
		*cwd = 0;
	elem->width = textw(dc, elem->text) -6;
	inputw += -elem->maxwidth + elem->width;

	Elem *e = malloc(sizeof(Elem));
	CIRCLEQ_INSERT_AFTER(&elemlist, elem, e, chain);
	memset(e->text, 0, BUFSIZ);
	cursor = 0;
	elem = e;
	e = elem->chain.cqe_prev;

	if(listdir() && e->dir == DIR_ISDIR) {
		e->dir = DIR_NODIR;
		e->text[--cursor] = 0;
		*cwd = 0;
	}
	inputw += elem->maxwidth;
	match();
}

void
insertselprefix() {
	Item *i;
	int len, plen;
	char ctmp, *tok;

	/* get prefix denominator of matches from current selection */
	i = matches;
	plen = strlen(sel->text);
	while(i) {
		if(i != sel)
			plen = pfxcmp(i->text, sel->text, plen);
		i = i->right;
	}
	/* insert prefix into input */
	cursor = 0;
	ctmp = sel->text[plen];
	sel->text[plen] = ' ';
	insert(sel->text, plen+1, False);
	sel->text[plen] = ctmp;
	cursor = plen;

	/* filter rest of input for substrings of prefix */
	len = strlen(elem->text);
	elem->text[cursor] = 0;
	tok = strtok(elem->text+cursor+1, " ");
	while(tok) {
		if(strstr(elem->text, tok)) {
			plen = strlen(tok);
			memcpy(tok, tok+plen+1, len - (tok-elem->text) - plen);
			len -= plen+1;
			plen = strlen(elem->text);
			if(len == plen)
				break;
			tok = strtok(tok, " ");
		}
		else {
			tok = strtok(0, " ");
			if(tok)
				tok[-1] = ' ';
		}
	}
	if(len > plen)
		elem->text[cursor] = ' ';

	elem->width = textw(dc, elem->text) -6;

}

void
keypress(XKeyEvent *ev) {
	char buf[32], *chr;
	int len;
	KeySym ksym = NoSymbol;
	Status status;
	Elem *e;

	len = XmbLookupString(xic, ev, buf, sizeof buf, &ksym, &status);
	if(status == XBufferOverflow)
		return;
	if(ev->state & ControlMask)
		switch(ksym) {
		case XK_a: ksym = XK_Home;      break;
		case XK_b: ksym = XK_Left;      break;
		case XK_c: ksym = XK_Escape;    break;
		case XK_d: ksym = XK_Delete;    break;
		case XK_e: ksym = XK_End;       break;
		case XK_f: ksym = XK_Right;     break;
		case XK_h: ksym = XK_BackSpace; break;
		case XK_i: ksym = XK_Tab;       break;
		case XK_j: ksym = XK_Return;    break;
		case XK_m: ksym = XK_Return;    break;
		case XK_n: ksym = XK_Down;      break;
		case XK_p: ksym = XK_Up;        break;

		case XK_k: /* delete right */
			elem->text[cursor] = '\0';
			match();
			break;
		case XK_u: /* delete left */
			insert(NULL, 0 - cursor, True);
			break;
		case XK_w: /* delete word */
			while(cursor > 0 && elem->text[nextrune(-1)] == ' ')
				insert(NULL, nextrune(-1) - cursor, True);
			while(cursor > 0 && elem->text[nextrune(-1)] != ' ')
				insert(NULL, nextrune(-1) - cursor, True);
			break;
		case XK_y: /* paste selection */
			XConvertSelection(dc->dpy, (ev->state & ShiftMask) ? clip : XA_PRIMARY,
				utf8, utf8, win, CurrentTime);
			return;
		default:
			return;
		}
	else if(ev->state & Mod1Mask)
		switch(ksym) {
		case XK_g: ksym = XK_Home;  break;
		case XK_G: ksym = XK_End;   break;
		case XK_h: ksym = XK_Up;    break;
		case XK_j: ksym = XK_Next;  break;
		case XK_k: ksym = XK_Prior; break;
		case XK_l: ksym = XK_Down;  break;
		default:
			return;
		}
	switch(ksym) {
	default:
		if(!iscntrl(*buf)) {
			tabsel = NULL;
			insert(buf, len, True);
		}
		break;
	case ' ':
		if(!*elem->text && elem != elemlist.cqh_first && elem->chain.cqe_prev->dir == DIR_ISDIR) {
			elem->chain.cqe_prev->dir = DIR_LAST;
			*cwd = 0;
			listdir();
			inputw += elem->maxwidth;
			match();
		}
		else {
			tabsel = NULL;
			insert(" ", 1, True);
		}
		break;
	case XK_Delete:
		if(elem->text[cursor] == '\0')
			return;
		cursor = nextrune(+1);
		/* fallthrough */
	case XK_BackSpace:
		if(cursor == 0) {
			if(elem == elemlist.cqh_first)
				return;
backspace:	e = elem->chain.cqe_prev;
			inputw -= elem->maxwidth + e->width;
			cursor = strlen(e->text);

			switch(e->dir) {
				case DIR_NODIR:
					*cwd = 0;
					break;
				case DIR_ISDIR:
					e->text[--cursor] = 0;
					e->dir = DIR_NODIR;
					cwd[cwdlen-1] = 0;
					chr = strrchr(cwd, '/');
					chr[1] = 0;
					cwdlen = chr-cwd+1;
					break;
				case DIR_LAST:
					e->text[--cursor] = 0;
					e->dir = DIR_NODIR;
					strcpy(cwd, e->path);
					cwdlen = strlen(cwd);
					break;
			}

			CIRCLEQ_REMOVE(&elemlist, elem, chain);
			elem = e;

			if(elem != elemlist.cqh_first)
				listdir();
			inputw += elem->maxwidth;
			match();
		}
		else
			insert(NULL, nextrune(-1) - cursor, True);
		tabsel = NULL;
		break;
	case XK_End:
		if(elem->text[cursor] != '\0') {
			cursor = strlen(elem->text);
			break;
		}
		if(next) {
			/* jump to end of list and position items in reverse */
			curr = matchend;
			calcoffsets();
			curr = prev;
			calcoffsets();
			while(next && (curr = curr->right))
				calcoffsets();
		}
		sel = matchend;
		break;
	case XK_Escape:
		cleanup(EXIT_FAILURE);
	case XK_Home:
		if(sel == matches) {
			cursor = 0;
			break;
		}
		sel = curr = matches;
		calcoffsets();
		break;
	case XK_Left:
		if(cursor > 0) {
			if(!sel || !sel->left || lines > 0) {
				cursor = nextrune(-1);
				break;
			}
		}
		else if(!strlen(elem->text) && elem != elemlist.cqh_first->chain.cqe_prev)
			goto backspace;
		else if(elem != elemlist.cqh_first && !sel->left) {
			e = elem->chain.cqe_prev;
			while(e->dir == DIR_ISDIR)
				e = e->chain.cqe_prev;
			elem->width = textw(dc, elem->text) -6;
			inputw += -elem->maxwidth + elem->width - e->width + e->maxwidth;
			cursor = strlen(e->text);
			if(e != elemlist.cqh_first) {
				if(e->dir == DIR_LAST) {
					e->text[--cursor] = 0;
					e->dir = DIR_NODIR;
				}
				strcpy(cwd, e->path);
				cwdlen = strlen(cwd);
				listdir();
			}
			elem = e;
			tabsel = NULL;
			match();
		}
		if(lines > 0)
			return;
		/* fallthrough */
	case XK_Up:
		if(sel && sel->left && (sel = sel->left)->right == curr) {
			curr = prev;
			calcoffsets();
		}
		break;
	case XK_Next:
		if(!next)
			return;
		sel = curr = next;
		calcoffsets();
		break;
	case XK_Prior:
		if(!prev)
			return;
		sel = curr = prev;
		calcoffsets();
		break;
	case XK_Return:
	case XK_KP_Enter:
		if(filecompletion) {
			Elem *e = elemlist.cqh_first;
			while(e != (void*)&elemlist) {
				if(!*e->text) {
					e = e->chain.cqe_next;
					continue;
				}
				if(e == elem && sel && !(ev->state & ShiftMask))
					printf("%s", sel->text);
				else
					printf("%s", e->text);
				if(e->dir != DIR_ISDIR)
					printf(" ");
				e = e->chain.cqe_next;
			}
			puts("");
		}
		else
			puts(sel && !(ev->state & ShiftMask) ? sel->text : elem->text);
		cleanup(EXIT_SUCCESS);
	case XK_Right:
		if(elem->text[cursor] != '\0') {
			cursor = nextrune(+1);
			break;
		}
		if(lines > 0)
			return;
		/* fallthrough */
	case XK_Down:
		if(sel && sel->right && (sel = sel->right) == next) {
			curr = next;
			calcoffsets();
		}
		break;
	case XK_Tab:
		if(!sel)
			return;
		if(!filecompletion) {
			strcpy(elem->text, sel->text);
			cursor = strlen(elem->text);
			match();
			break;
		}
		if(sel == tabsel || matches == matchend || exactmatch) {
			newelem();
			break;
		}

		tabsel = sel;
		insertselprefix();
		match();
		if(matches == matchend)
			newelem();
		break;
	}
	drawmenu();
}

void
match(void) {
	static char **tokv = NULL;
	static int tokn = 0;

	char buf[BUFSIZ], *s;
	int i, tokc = 0;
	size_t len;
	Item *item, *lprefix, *lsubstr, *prefixend, *substrend, *citems;

	citems = items;
	if(elem != elemlist.cqh_first)
		citems = fitems;

	strcpy(buf, elem->text);
	/* separate input text into tokens to be matched individually */
	for(s = strtok(buf, " "); s; tokv[tokc-1] = s, s = strtok(NULL, " "))
		if(++tokc > tokn && !(tokv = realloc(tokv, ++tokn * sizeof *tokv)))
			eprintf("cannot realloc %u bytes\n", tokn * sizeof *tokv);
	len = tokc ? strlen(tokv[0]) : 0;

	matches = lprefix = lsubstr = matchend = prefixend = substrend = NULL;
	exactmatch = False;

	if(tabsel)
		appenditem(tabsel, &matches, &matchend);

	for(item = citems; item && item->text; item++) {
		if(tabsel == item)
			continue;
		for(i = 0; i < tokc; i++)
			if(!fstrstr(item->text, tokv[i]))
				break;
		if(i != tokc) /* not all tokens match */
			continue;
		/* exact matches go first, then prefixes, then substrings */
		if(!tokc || !fstrncmp(tokv[0], item->text, len+1)) {
			exactmatch = True;
			appenditem(item, &matches, &matchend);
		}
		else if(!fstrncmp(tokv[0], item->text, len))
			appenditem(item, &lprefix, &prefixend);
		else
			appenditem(item, &lsubstr, &substrend);
	}
	if(lprefix) {
		if(matches) {
			matchend->right = lprefix;
			lprefix->left = matchend;
		}
		else
			matches = lprefix;
		matchend = prefixend;
	}
	if(lsubstr) {
		if(matches) {
			matchend->right = lsubstr;
			lsubstr->left = matchend;
		}
		else
			matches = lsubstr;
		matchend = substrend;
	}
	curr = sel = matches;
	calcoffsets();
}

size_t
nextrune(int inc) {
	ssize_t n;

	/* return location of next utf8 rune in the given direction (+1 or -1) */
	for(n = cursor + inc; n + inc >= 0 && (elem->text[n] & 0xc0) == 0x80; n += inc);
	return n;
}

void
paste(void) {
	char *p, *q;
	int di;
	unsigned long dl;
	Atom da;

	/* we have been given the current selection, now insert it into input */
	XGetWindowProperty(dc->dpy, win, utf8, 0, (BUFSIZ / 4) + 1, False,
	                   utf8, &da, &di, &dl, &dl, (unsigned char **)&p);
	insert(p, (q = strchr(p, '\n')) ? q-p : (ssize_t)strlen(p), True);
	XFree(p);
	drawmenu();
}

void
readstdin(void) {
	char buf[BUFSIZ], *p, *maxstr = NULL;
	size_t i, max = 0, size = 0;

	/* read each line from stdin and add it to the item list */
	for(i = 0; fgets(buf, sizeof buf, stdin); i++) {
		if(i+1 >= size / sizeof *items)
			if(!(items = realloc(items, (size += BUFSIZ))))
				eprintf("cannot realloc %u bytes:", size);
		if((p = strchr(buf, '\n')))
			*p = '\0';
		if(!(items[i].text = strdup(buf)))
			eprintf("cannot strdup %u bytes:", strlen(buf)+1);
		if(strlen(items[i].text) > max)
			max = strlen(maxstr = items[i].text);
	}
	if(items)
		items[i].text = NULL;
	inputw = maxstr ? textw(dc, maxstr) : 0;
	lines = MIN(lines, i);
}

int
listdir(void) {
	size_t i, max = 0;
	DIR *dp;
	struct dirent *ep;
	char *maxstr = NULL;
	char *path = *cwd ? cwd : pwd, *ptr, *ptr2;
	int num;

	dp = opendir(path);
	if(!dp) {
		switch(errno) {
			case EACCES: printf("file: permission denied: %s\n", path); break;
			case ENOENT: printf("file: cwd unlinked: %s\n", path); break;
			case ENOTDIR: printf("file: cwd not directory: %s\n", path); break;
		}
		if(fitems)
			free(fitems);
		fitems = 0;
		fsize = 0;
		return 1;
	}

	for(i = 0; (ep = readdir(dp)); i++) {
		if(i+1 >= fsize / sizeof *fitems)
			if(!(fitems = realloc(fitems, (fsize += BUFSIZ))))
				eprintf("cannot realloc %u bytes:", fsize);
		for(num = 0, ptr = ep->d_name; (ptr = strchr(ptr, ' ')); num++, ptr++);
		if(!num) {
			if(!(fitems[i].text = strdup(ep->d_name)))
				eprintf("cannot strdup %u bytes:", strlen(ep->d_name)+1);
		}
		else {
			fitems[i].text = malloc(strlen(ep->d_name)+num);
			ptr = strtok(ep->d_name, " ");
			ptr2 = fitems[i].text;
			while(1) {
				strcpy(ptr2, ptr);
				ptr2 += strlen(ptr)+2;
				ptr = strtok(0, " ");
				if(ptr)
					strcpy(ptr2-2, "\\ ");
				else
					break;
			}
		}
		if(strlen(fitems[i].text) > max)
			max = strlen(maxstr = fitems[i].text);
	}
	if(fitems)
		fitems[i].text = NULL;

	closedir(dp);
	lines = MIN(lines, i);
	elem->maxwidth = maxstr ? textw(dc, maxstr) +6 : 0;
	elem->dir = DIR_NODIR;
	elem->width = textw(dc, elem->text) -6;
	strcpy(elem->path, path);

	return 0;
}

void
run(void) {
	XEvent ev;

	while(!XNextEvent(dc->dpy, &ev)) {
		if(XFilterEvent(&ev, win))
			continue;
		switch(ev.type) {
		case Expose:
			if(ev.xexpose.count == 0)
				mapdc(dc, win, mw, mh);
			break;
		case KeyPress:
			keypress(&ev.xkey);
			break;
		case SelectionNotify:
			if(ev.xselection.property == utf8)
				paste();
			break;
		case VisibilityNotify:
			if(ev.xvisibility.state != VisibilityUnobscured)
				XRaiseWindow(dc->dpy, win);
			break;
		}
	}
}

void
setup() {
	int x, y, screen = DefaultScreen(dc->dpy);
	Window root = RootWindow(dc->dpy, screen);
	XSetWindowAttributes swa;
	XIM xim;
#ifdef XINERAMA
	int n;
	XineramaScreenInfo *info;
#endif

	normcol[ColBG] = getcolor(dc, normbgcolor);
	normcol[ColFG] = getcolor(dc, normfgcolor);
	selcol[ColBG]  = getcolor(dc, selbgcolor);
	selcol[ColFG]  = getcolor(dc, selfgcolor);

	clip = XInternAtom(dc->dpy, "CLIPBOARD", False);
	utf8 = XInternAtom(dc->dpy, "UTF8_STRING", False);

	CIRCLEQ_INIT(&elemlist);
	elem = malloc(sizeof(Elem));
	CIRCLEQ_INSERT_HEAD(&elemlist, elem, chain);
	memset(elem->text, 0, BUFSIZ);
	elem->dir = DIR_NODIR;
	elem->maxwidth = inputw;

	if(filecompletion) {
		if(!getcwd(pwd, PATH_MAX))
			switch(errno) {
				case EACCES: printf("file: permission denied\n"); break;
				case ENOENT: printf("file: pwd unlinked\n"); break;
				case ERANGE: printf("file: path too long\n"); break;
			}
		pwd[strlen(pwd)] = '/';
	}

	/* calculate menu geometry */
	bh = dc->font.height + 2;
	lines = MAX(lines, 0);
	mh = (lines + 1) * bh;
#ifdef XINERAMA
	if((info = XineramaQueryScreens(dc->dpy, &n))) {
		int a, j, di, i = 0, area = 0;
		unsigned int du;
		Window w, pw, dw, *dws;
		XWindowAttributes wa;

		XGetInputFocus(dc->dpy, &w, &di);
		if(w != root && w != PointerRoot && w != None) {
			/* find top-level window containing current input focus */
			do {
				if(XQueryTree(dc->dpy, (pw = w), &dw, &w, &dws, &du) && dws)
					XFree(dws);
			} while(w != root && w != pw);
			/* find xinerama screen with which the window intersects most */
			if(XGetWindowAttributes(dc->dpy, pw, &wa))
				for(j = 0; j < n; j++)
					if((a = INTERSECT(wa.x, wa.y, wa.width, wa.height, info[j])) > area) {
						area = a;
						i = j;
					}
		}
		/* no focused window is on screen, so use pointer location instead */
		if(!area && XQueryPointer(dc->dpy, root, &dw, &dw, &x, &y, &di, &di, &du))
			for(i = 0; i < n; i++)
				if(INTERSECT(x, y, 1, 1, info[i]))
					break;

		x = info[i].x_org;
		y = info[i].y_org + (topbar ? 0 : info[i].height - mh);
		mw = info[i].width;
		XFree(info);
	}
	else
#endif
	{
		x = 0;
		y = topbar ? 0 : DisplayHeight(dc->dpy, screen) - mh;
		mw = DisplayWidth(dc->dpy, screen);
	}
	promptw = prompt ? textw(dc, prompt) : 0;
	elem->maxwidth = MIN(elem->maxwidth, mw/3);
	match();

	/* create menu window */
	swa.override_redirect = True;
	swa.background_pixel = normcol[ColBG];
	swa.event_mask = ExposureMask | KeyPressMask | VisibilityChangeMask;
	win = XCreateWindow(dc->dpy, root, x, y, mw, mh, 0,
		DefaultDepth(dc->dpy, screen), CopyFromParent,
		DefaultVisual(dc->dpy, screen),
		CWOverrideRedirect | CWBackPixel | CWEventMask, &swa);

	/* open input methods */
	xim = XOpenIM(dc->dpy, NULL, NULL, NULL);
	xic = XCreateIC(xim, XNInputStyle, XIMPreeditNothing | XIMStatusNothing,
		XNClientWindow, win, XNFocusWindow, win, NULL);

	XMapRaised(dc->dpy, win);
	resizedc(dc, mw, mh);
	drawmenu();
}

void
usage(void) {
	fputs("usage: dmenu [-b] [-f] [-i] [-l lines] [-p prompt] [-fn font]\n"
		  "             [-nb color] [-nf color] [-sb color] [-sf color] [-v] [-fc]\n", stderr);
	exit(EXIT_FAILURE);
}
