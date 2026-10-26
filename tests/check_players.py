"""The animation player exists twice: as a string in Slides/Backend/Reveal.agda (reveal.js
backend) and in assets/plain.js (standalone backend).  Their frame-rebuilding code must
be the same text: the functions from `parse` to `draw`, whitespace aside."""
import re, sys

def functions(lines):
    text = "\n".join(l.strip() for l in lines)
    a = text.index("function parse")
    b = min(text.find(m, a) for m in ("function target", "function show") if text.find(m, a) >= 0)
    return re.sub(r"\s+", " ", text[a:b]).strip()

plain = functions(open("assets/plain.js").read().splitlines())
agda = []
for l in open("src/Slides/Backend/Reveal.agda").read().splitlines():
    m = re.match(r'^\s*"(.*)\\n" \+\+ˢ\s*$', l)
    if m:
        agda.append(m.group(1).replace('\\"', '"').replace("\\\\", "\\"))
reveal = functions(agda)
if plain != reveal:
    import difflib
    for d in difflib.unified_diff(plain.split("; "), reveal.split("; "), "plain.js", "Reveal.agda", lineterm=""):
        print(d)
    sys.exit("the two animation players differ")
print("ok   both players share their frame-rebuilding code")
