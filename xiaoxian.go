package xiaoxian

import (
	"bytes"
	"fmt"
	"io/ioutil"
	"net/http"
	"net/url"
	"regexp"
	"strings"
	"time"

	"github.com/stretchr/objx"
	tk "github.com/topxeq/txtk"
	"github.com/wangbin/jiebago"
	"github.com/wangbin/jiebago/posseg"
)

const XiaoXianHost = "topget.org:7482"
const XiaoXianDefaultTid = "tc040626"

func CleanEnglish(sentA string) string {
	rs := tk.Replace(sentA, "“", "\"")
	rs = tk.Replace(rs, "”", "\"")
	rs = tk.Replace(rs, "。", ".")
	rs = tk.Replace(rs, "．", ".")
	rs = tk.Replace(rs, "！", "!")
	rs = tk.Replace(rs, "？", "?")
	rs = tk.Replace(rs, "﹖", "?")
	rs = tk.Replace(rs, "（", "(")
	rs = tk.Replace(rs, "）", ")")
	rs = tk.Replace(rs, "，", ",")
	rs = tk.Replace(rs, "–", "-")
	rs = tk.Replace(rs, "—", "TX--TX")
	rs = tk.Replace(rs, "‘", "'")
	rs = tk.Replace(rs, "’", "'")
	rs = tk.Replace(rs, "：", ":")
	rs = tk.Replace(rs, "…", "...")
	rs = tk.Replace(rs, "\\xa0", " ")
	rs = tk.Replace(rs, "TX--TX", "—")
	rs = tk.Trim(rs)
	rs = tk.RegReplace(rs, `\s+`, " ")

	return rs
}

func CleanChineseSentence(sentA string) string {
	rs := tk.Replace(sentA, "\r", "")
	rs = tk.Replace(rs, "\"", "“")
	rs = tk.Replace(rs, "!", "！")
	rs = tk.Replace(rs, "?", "？")
	rs = tk.Replace(rs, "(", "（")
	rs = tk.Replace(rs, ")", "）")
	rs = tk.Replace(rs, ",", "，")
	rs = tk.Replace(rs, ":", "：")
	rs = tk.Trim(rs)
	rs = tk.RegReplace(rs, "\\s+", " ")

	return rs
}

func EnsureValidEnglishOnly(textA string, ifOtherEmptyA bool) string {
	rs := tk.Replace(textA, "\r", "")
	rs = tk.Replace(rs, "\u00e9", "\x0f")
	rs = tk.Replace(rs, "\u00e8", "\x10")
	rs = tk.Replace(rs, "\u2103", "°C") // u2103
	rs = tk.Replace(rs, "\u00b0", "\x11")
	rs = tk.Replace(rs, "\u00d7", "x")
	rs = tk.Replace(rs, "\u2013", "-")
	rs = tk.Replace(rs, "\u2014", "-")
	rs = tk.Replace(rs, "\u2018", "'")
	rs = tk.Replace(rs, "\u2019", "'")
	rs = tk.Replace(rs, "\u201c", "\"")
	rs = tk.Replace(rs, "\u201d", "\"")
	rs = tk.Replace(rs, "\u201f", "\"")
	rs = tk.Replace(rs, "\u2022", "\x12")
	rs = tk.Replace(rs, "\u2026", "...")
	rs = tk.Replace(rs, "\u2028", "\x1e")
	rs = tk.Replace(rs, "\u221a", "\x02")
	rs = tk.Replace(rs, "\u2500", "-")
	rs = tk.Replace(rs, "\u25CF", "*")
	rs = tk.Replace(rs, "\u3001", ",")
	rs = tk.Replace(rs, "\u3000", " ")
	rs = tk.Replace(rs, "\ufeff", "")
	rs = tk.Replace(rs, "\uff0a", "*")
	rs = tk.Replace(rs, "\uff01", "!")
	rs = tk.Replace(rs, "\uff0c", ",")
	rs = tk.Replace(rs, "\uff0d", "-")
	rs = tk.Replace(rs, "\uff0e", ".")
	rs = tk.Replace(rs, "\uff1a", ":")
	rs = tk.Replace(rs, "\uff1f", "?")
	rs = tk.Replace(rs, "\uffe1", "\x0e")

	if ifOtherEmptyA {
		rs = tk.RegReplace(rs, `[\p{Han}]`, "\x03")
	}

	return rs
}

// a modified version of treebank tokenizer start
type TreebankWordTokenizer struct {
	initialized bool
	steps       []step
}

type step struct {
	Regexp      *regexp.Regexp
	Replacement string
	Literal     bool
}

func (t *TreebankWordTokenizer) init() {
	steps := make([]step, 0, 25)

	// Starting quotes.
	steps = append(
		steps,
		// Starting quotes.
		step{regexp.MustCompile(`^"`), "``", true},
		step{regexp.MustCompile("(``)"), " ${1} ", false},
		step{regexp.MustCompile(`([ (\[{<])"`), "${1} `` ", false},

		// Punctuation.
		step{regexp.MustCompile(`(—+)`), " ${1} ", false},
		step{regexp.MustCompile(`([^—])([—])([^—])`), "${1} ${2} ${3}", false},
		//		step{regexp.MustCompile(`([:,—])([^\d])`), " ${1} ${2}", false},
		step{regexp.MustCompile(`([^\.][^\.A_Z])(\.)([\]\)}>"']*)\s*$`), "${1} ${2}${3} ", false},
		step{regexp.MustCompile(`(\sI)(\.)([\]\)}>"']*)\s*$`), "${1} ${2}${3} ", false},
		step{regexp.MustCompile(`(\s+|^)([^\.\s]*)(\.)([\]\)}>"']*)\s*$`), " ${2} ${3}${4} ", false},
		step{regexp.MustCompile(`(\s+|^)([^\.\s]+)(\.)([\]\)}>"']*)\s+(\S)`), " ${2} ${3}${4} ${5}", false},
		step{regexp.MustCompile(`(\s+|^)([^\.\s]+)(\.)([\]\)}>"']*)\s+(\S)`), " ${2} ${3}${4} ${5}", false},

		step{regexp.MustCompile(`([:,])([^\d])`), " ${1} ${2}", false},
		step{regexp.MustCompile(`([:,])$`), " ${1} ", false},
		step{regexp.MustCompile(`(\d*[^\d\s]\d*),$`), "${1} ,", false},
		step{regexp.MustCompile(`\.\.\.`), " ... ", true},
		step{regexp.MustCompile(`[;@#$%&]`), " ${0} ", false},
		step{regexp.MustCompile(`[?!]`), " ${0} ", false},
		step{regexp.MustCompile(` '([^']+)' `), " ' ${1} ' ", false},    // added by TopXeQ, for "... migrants, in contrast to its earlier 'open-door' policy."
		step{regexp.MustCompile(`(?m) '([^']+)'$`), " ' ${1} '", false}, // added by TopXeQ, for "... Feel young again in 'Old Florida'"
		step{regexp.MustCompile(`(?m)^'([^']+)' `), "' ${1} ' ", false}, // added by TopXeQ, for "'Old Florida' ..."
		step{regexp.MustCompile(`([^'])' `), "${1} ' ", false},
		step{regexp.MustCompile(`(\s)'(\S)`), "${1} ' ${2}", false},
		step{regexp.MustCompile(`^'(\S)`), " ' ${1}", false},
		step{regexp.MustCompile(`(\s+[^']+)'$`), "${1} '", false},

		// Brackets and stuff.
		step{regexp.MustCompile(`[\]\[\(\)\{\}\<\>]`), " ${0} ", false},
		step{regexp.MustCompile(`--`), " -- ", true},

		// Ending quotes.
		step{regexp.MustCompile(`"`), " '' ", true},
		step{regexp.MustCompile(`(\S)('')`), "${1} ${2} ", false},

		// Contractions 1.
		step{regexp.MustCompile(`([^' ])('[sS]|'[mM]|'[dD]|') `), "${1} ${2} ", false},
		step{regexp.MustCompile(`Ain't you`), "are not you ", false}, // added by TopXeQ
		step{regexp.MustCompile(`([^' ])('ll|'LL|'re|'RE|'ve|'VE|n't|N'T) `), "${1} ${2} ", false},
		step{regexp.MustCompile(`^(')([^'\s]*\s)`), "${1} ${2}", false},         // added by topxeq
		step{regexp.MustCompile(`(\s')([^'sltrvdm\s]*\s)`), "${1} ${2}", false}, // added by topxeq

		// Contractions 2.
		step{regexp.MustCompile(`(?i)\b(can)(not)\b`), " ${1} ${2} ", false},
		step{regexp.MustCompile(`(?i)\b(d)('ye)\b`), " ${1} ${2} ", false},
		step{regexp.MustCompile(`(?i)\b(gim)(me)\b`), " ${1} ${2} ", false},
		step{regexp.MustCompile(`(?i)\b(gon)(na)\b`), " ${1} ${2} ", false},
		step{regexp.MustCompile(`(?i)\b(got)(ta)\b`), " ${1} ${2} ", false},
		step{regexp.MustCompile(`(?i)\b(lem)(me)\b`), " ${1} ${2} ", false},
		step{regexp.MustCompile(`(?i)\b(mor)('n)\b`), " ${1} ${2} ", false},
		step{regexp.MustCompile(`(?i)\b(wan)(na)\s`), " ${1} ${2} ", false},

		// Contractions 3.
		step{regexp.MustCompile(`(?i) ('t)(is)\b`), " ${1} ${2} ", false},
		step{regexp.MustCompile(`(?i) ('t)(was)\b`), " ${1} ${2} ", false},

		// Clean up whitespaces.
		step{regexp.MustCompile(`\s`), " ", false},
		step{regexp.MustCompile(`\s+`), " ", false},
	)

	(*t).steps = steps
	(*t).initialized = true
}

func (t *TreebankWordTokenizer) Tokenize(text string) []string {
	if !(*t).initialized {
		t.init()
	}

	_text := text
	for _, step := range (*t).steps {
		if step.Literal {
			_text = step.Regexp.ReplaceAllLiteralString(_text, step.Replacement)
		} else {
			_text = step.Regexp.ReplaceAllString(_text, step.Replacement)
		}
		//		TXLogMemOneTimeWithTime("%v -> %v", step.Regexp.String(), _text)
	}

	_text = tk.Replace(_text, "``", "\"")
	//	_text = TXReplace(_text, "''", "\"'")
	_text = tk.Replace(_text, "''", "\"")
	_text = strings.TrimSpace(_text)
	return strings.Split(_text, " ")
}

func (t *TreebankWordTokenizer) TokenizeWithDetail(text string) []string {
	if !(*t).initialized {
		t.init()
	}

	rs := make([]string, 0)

	_text := text
	for i, step := range (*t).steps {
		if step.Literal {
			_text = step.Regexp.ReplaceAllLiteralString(_text, step.Replacement)
			rs = append(rs, fmt.Sprintf("%v %v %v %v: %v", i, step.Literal, step.Regexp, step.Replacement, _text))
		} else {
			_text = step.Regexp.ReplaceAllString(_text, step.Replacement)
			rs = append(rs, fmt.Sprintf("%v %v %v %v: %v", i, step.Literal, step.Regexp, step.Replacement, _text))
		}
	}
	return rs
}

func NewTreebankWordTokenizer() *TreebankWordTokenizer {
	t := new(TreebankWordTokenizer)
	t.init()
	return t
}

// treebank tokenizer end

type TokenizerCn struct {
	segM *jiebago.Segmenter
}

func NewTokenizerCn(dictA string, userDictA string) (*TokenizerCn, error) {
	if !tk.IfFileExists(dictA) {
		return nil, fmt.Errorf("file not exists")
	}

	p := new(TokenizerCn)

	p.segM = new(jiebago.Segmenter)

	errT := p.segM.LoadDictionary(dictA)

	if errT != nil {
		return nil, errT
	}

	if userDictA != "" {
		errT = p.segM.LoadUserDictionary(userDictA)

		if errT != nil {
			return nil, errT
		}
	}

	return p, nil
}

func (p *TokenizerCn) LoadDict(dictA string) error {
	return p.segM.LoadDictionary(dictA)
}

func (p *TokenizerCn) LoadUserDict(userDictA string) error {
	return p.segM.LoadUserDictionary(userDictA)
}

func (p *TokenizerCn) Tokenize(strA string, autoA bool) []string {
	cutResultT := p.segM.Cut(strA, autoA)

	listT := make([]string, 0, 10)

	for wordT := range cutResultT {
		listT = append(listT, wordT)
	}

	return listT
}

type PosTaggerCn struct {
	segM *posseg.Segmenter
}

func NewPosTaggerCn(dictA string, userDictA string) (*PosTaggerCn, error) {
	if !tk.IfFileExists(dictA) {
		return nil, fmt.Errorf("file not exists")
	}

	p := new(PosTaggerCn)

	p.segM = new(posseg.Segmenter)

	errT := p.segM.LoadDictionary(dictA)

	if errT != nil {
		return nil, errT
	}

	if userDictA != "" {
		errT = p.segM.LoadUserDictionary(userDictA)

		if errT != nil {
			return nil, errT
		}
	}

	return p, nil
}

func (p *PosTaggerCn) LoadDict(dictA string) error {
	return p.segM.LoadDictionary(dictA)
}

func (p *PosTaggerCn) LoadUserDict(userDictA string) error {
	return p.segM.LoadUserDictionary(userDictA)
}

func (p *PosTaggerCn) Tag(strA string, autoA bool, sepA string) []string {
	cutResultT := p.segM.Cut(strA, autoA)

	listT := make([]string, 0, 10)

	if sepA == "" {
		sepA = "`"
	}

	for segT := range cutResultT {
		listT = append(listT, segT.Text()+sepA+segT.Pos())
	}

	return listT
}

// SplitArticleEn 英语分句
func SplitArticleEn(strA string) []string {
	ts := tk.RegReplace(" "+strA, `(\sU)\.\S\.(\s)`, "$1`DOT~S`DOT~$2")
	ts = tk.RegReplace(ts, ".! ", "|")
	ts = tk.RegReplace(ts, "(\\s)(\\d+)\\.(\\s)", "$1$2`DOT~$3")
	ts = tk.RegReplace(ts[1:], `([\.?!;]["']?)\s+(["'A-Z0-9])`, "$1|$2")
	ts = tk.RegReplace(ts, "`DOT~", ".")

	return strings.Split(ts, "|")
}

func SplitArticleEnOL(strA string) ([]string, error) {
	urlT := XiaoXianHost + "/japi"

	paramsT := url.Values{}

	paramsT.Set("txreq", "splitArticle")
	paramsT.Set("tid", XiaoXianDefaultTid)
	paramsT.Set("article", strA)

	responseT := tk.DownloadPageUTF8(urlT, paramsT, "", 15)

	if tk.IsErrorString(responseT) {
		return nil, fmt.Errorf("%v", tk.GetErrorString(responseT))
	}

	resultT, errT := tk.TXResultFromString(responseT)

	if errT != nil {
		return nil, errT
	}

	if resultT.Status != "success" {
		return nil, fmt.Errorf("%v", resultT.Value)
	}

	return strings.Split(resultT.Value, "\n"), nil
}

func SplitArticleCn(strA string) []string {
	ts := tk.RegReplace(" "+strA, `(\sU)\.\S\.(\s)`, "$1`DOT~S`DOT~$2")
	ts = tk.RegReplace(ts, ".! ", "|")
	ts = tk.RegReplace(ts, `(\s)(\\d+)\.(\s)`, "$1$2`DOT~$3")
	ts = tk.RegReplace(ts[1:], `([\.?!;。？！]["'“‘”’]?)\s+(["'“‘”’A-Z0-9\p{Han}])`, "$1|$2")
	ts = tk.RegReplace(ts, "`DOT~", ".")

	ts = tk.RegReplace(ts, `([。！？\?])([^”’])`, `${1}|${2}`)
	ts = tk.RegReplace(ts, `(\.{6})([^”’])`, `${1}|${2}`)
	ts = tk.RegReplace(ts, `(\…{2})([^”’])`, `${1}|${2}`)
	ts = tk.RegReplace(ts, `([。！？\?][”’])([^，。！？\?])`, `${1}|${2}`)

	return strings.Split(ts, "|")
}

func TokenizeEn(strA string) []string {
	tokenizer := NewTreebankWordTokenizer()

	return tokenizer.Tokenize(strA)
}

func TokenizeEnOL(strA string) ([]string, error) {
	urlT := XiaoXianHost + "/japi"

	paramsT := url.Values{}

	paramsT.Set("txreq", "tokenize")
	paramsT.Set("tid", XiaoXianDefaultTid)
	paramsT.Set("sent", strA)
	paramsT.Set("sep", "\n") // 指定结果用什么分隔符

	responseT := tk.DownloadPageUTF8(urlT, paramsT, "", 15)

	if tk.IsErrorString(responseT) {
		return nil, fmt.Errorf("%v", tk.GetErrorString(responseT))
	}

	resultT, errT := tk.TXResultFromString(responseT)

	if errT != nil {
		return nil, errT
	}

	if resultT.Status != "success" {
		return nil, fmt.Errorf("%v", resultT.Value)
	}

	return strings.Split(resultT.Value, "\n"), nil
}

func TagEnOL(strA string) ([]string, error) {
	urlT := XiaoXianHost + "/japi"

	paramsT := url.Values{}

	paramsT.Set("txreq", "analyzeSentEx")
	paramsT.Set("tid", XiaoXianDefaultTid)
	paramsT.Set("sent", strA)

	responseT := tk.DownloadPageUTF8(urlT, paramsT, "", 15)

	if tk.IsErrorString(responseT) {
		return nil, fmt.Errorf("%v", tk.GetErrorString(responseT))
	}

	resultT, errT := tk.TXResultFromString(responseT)

	if errT != nil {
		return nil, errT
	}

	if resultT.Status != "success" {
		return nil, fmt.Errorf("%v", resultT.Value)
	}

	return strings.Split(strings.Trim(resultT.Value, "_"), "_"), nil
}

func GetNamedEntityEnOL(strA string) ([]string, error) {
	urlT := XiaoXianHost + "/japi"

	paramsT := url.Values{}

	paramsT.Set("txreq", "getNamedEntities")
	paramsT.Set("tid", XiaoXianDefaultTid)
	paramsT.Set("sent", strA)

	responseT := tk.DownloadPageUTF8(urlT, paramsT, "", 15)

	if tk.IsErrorString(responseT) {
		return nil, fmt.Errorf("%v", tk.GetErrorString(responseT))
	}

	resultT, errT := tk.TXResultFromString(responseT)

	if errT != nil {
		return nil, errT
	}

	if resultT.Status != "success" {
		return nil, fmt.Errorf("%v", resultT.Value)
	}

	return strings.Split(resultT.Value, "|"), nil
}

func GetArticleDifficultyEnOL(strA string) (string, error) {
	urlT := XiaoXianHost + "/japi"

	paramsT := url.Values{}

	paramsT.Set("txreq", "analyzeArticleDifficulty")
	paramsT.Set("tid", XiaoXianDefaultTid)
	paramsT.Set("article", strA)

	responseT := tk.DownloadPageUTF8(urlT, paramsT, "", 15)

	if tk.IsErrorString(responseT) {
		return "", fmt.Errorf("%v", tk.GetErrorString(responseT))
	}

	resultT, errT := tk.TXResultFromString(responseT)

	if errT != nil {
		return "", errT
	}

	if resultT.Status != "success" {
		return "", fmt.Errorf("%v", resultT.Value)
	}

	return resultT.Value, nil
}

func ParseSentenceEnOL(strA string) (string, error) {
	urlT := XiaoXianHost + "/japi"

	paramsT := url.Values{}

	paramsT.Set("txreq", "parseSentExCompact")
	paramsT.Set("tid", XiaoXianDefaultTid)
	paramsT.Set("sent", strA)

	responseT := tk.DownloadPageUTF8(urlT, paramsT, "", 15)

	if tk.IsErrorString(responseT) {
		return "", fmt.Errorf("%v", tk.GetErrorString(responseT))
	}

	resultT, errT := tk.TXResultFromString(responseT)

	if errT != nil {
		return "", errT
	}

	if resultT.Status != "success" {
		return "", fmt.Errorf("%v", resultT.Value)
	}

	return resultT.Value, nil
}

func DownloadPagePostOnlyBaiduNLP(tokenA string, ifCustomA bool, postDataA string, timeoutSecsA time.Duration) string {
	client := &http.Client{
		Timeout: time.Second * timeoutSecsA,
	}

	var urlT string

	if ifCustomA {
		urlT = "https://aip.baidubce.com/rpc/2.0/nlp/v1/lexer_custom?access_token=" + tokenA
	} else {
		urlT = "https://aip.baidubce.com/rpc/2.0/nlp/v1/lexer?access_token=" + tokenA
	}

	var respT *http.Response
	var errT error

	respT, errT = client.Post(urlT, "application/json", bytes.NewBufferString(tk.ConvertToGB18030(postDataA)))

	if errT == nil {
		defer respT.Body.Close()
		if respT.StatusCode != 200 {
			return tk.GenerateErrorStringF("response status: %v", respT.StatusCode)
		} else {
			body, errT := ioutil.ReadAll(respT.Body)

			if errT == nil {
				return tk.ConvertToUTF8(body, "GBK")
			} else {
				return tk.GenerateErrorString(errT.Error())
			}
		}
	} else {
		return tk.GenerateErrorString(errT.Error())
	}
}

func TokenizeCnBaiduOL(textA string, ifCustomA bool, tokenA string, clientIdA string, clientSecretA string) (rs string, err string, token string) {
	textT := strings.TrimSpace(textA)
	if textT == "" {
		return "", "empty text", ""
	}

	if tokenA == "" {
		urlT := "https://aip.baidubce.com/oauth/2.0/token?grant_type=client_credentials&client_id=" + clientIdA + "&client_secret=" + clientSecretA

		rs := tk.DownloadPage(urlT, "GBK", nil, "", 15)

		matchT := tk.RegFindFirst(rs, `"access_token":"([^"]*)"`, 1)

		if tk.IsErrorString(matchT) {
			return "", tk.GetErrorString(matchT), ""
		}

		tokenA = matchT
	}

	textT = CleanChineseSentence(textA)

	rs = DownloadPagePostOnlyBaiduNLP(tokenA, ifCustomA, tk.ObjectToJSON(map[string]string{"text": textT}), 15)

	m, errT := objx.FromJSON(rs)

	if errT != nil {
		return "", errT.Error(), ""
	}

	mi := m.Get("items").MSISlice()

	var tmpsl = make([]string, 0)

	for _, v := range mi {
		tmpss := v["item"].(string)

		tmpsl = append(tmpsl, tmpss)
	}

	return strings.Join(tmpsl, " "), "", tokenA
}

func NerCnBaiduOL(textA string, ifCustomA bool, tokenA string, clientIdA string, clientSecretA string) (rs string, err string, token string) {
	textT := strings.TrimSpace(textA)
	if textT == "" {
		return "", "empty text", ""
	}

	if tokenA == "" {
		urlT := "https://aip.baidubce.com/oauth/2.0/token?grant_type=client_credentials&client_id=" + clientIdA + "&client_secret=" + clientSecretA

		rs := tk.DownloadPage(urlT, "GBK", nil, "", 15)

		matchT := tk.RegFindFirst(rs, `"access_token":"([^"]*)"`, 1)

		if tk.IsErrorString(matchT) {
			return "", tk.GetErrorString(matchT), ""
		}

		tokenA = matchT
	}

	textT = CleanChineseSentence(textA)

	rs = DownloadPagePostOnlyBaiduNLP(tokenA, ifCustomA, tk.ObjectToJSON(map[string]string{"text": textT}), 15)

	m, errT := objx.FromJSON(rs)

	if errT != nil {
		return "", errT.Error(), ""
	}

	mi := m.Get("items").MSISlice()

	var tmpsl = make([]string, 0)

	for _, v := range mi {
		tmpss := v["item"].(string)
		tmpner := v["ne"].(string)

		if tmpner == "" {
			continue
		}

		tmpsl = append(tmpsl, tmpss+"`"+tmpner)
	}

	return strings.Join(tmpsl, " "), "", tokenA
}
