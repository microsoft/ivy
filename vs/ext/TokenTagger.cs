using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Linq;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;
using System.Diagnostics.Contracts;


namespace IvyLanguage
{

  #region Provider

  [Export(typeof(ITaggerProvider))]
  [ContentType("ivy")]
  [TagType(typeof(IvyTokenTag))]
  internal sealed class IvyTokenTagProvider : ITaggerProvider
  {
    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      return new IvyTokenTagger(buffer) as ITagger<T>;
    }
  }

  #endregion


  #region Tagger

  public enum IvyTokenKind
  {
    Keyword, BuiltInType, Number, String, Comment, VariableIdentifier
  }

  public class IvyTokenTag : ITag
  {
    public IvyTokenKind Kind { get; private set; }
    public string HoverText
    {
      get
      {
        string text = "";
        return text;
      }
    }

    public IvyTokenTag(IvyTokenKind kind) {
      this.Kind = kind;
    }

  }


  internal sealed class IvyTokenTagger : ITagger<IvyTokenTag>, IDisposable
  {
    internal sealed class ScanResult
    {
      internal ITextSnapshot _oldSnapshot; 
      internal ITextSnapshot _newSnapshot; 
      internal List<TokenRegion> _regions; // the regions computed for the _newSnapshot
      internal NormalizedSnapshotSpanCollection _difference; // the difference between _oldSnapshot and _newSnapshot

      internal ScanResult(ITextSnapshot oldSnapshot, ITextSnapshot newSnapshot, List<TokenRegion> regions, NormalizedSnapshotSpanCollection diffs) {
        _oldSnapshot = oldSnapshot;
        _newSnapshot = newSnapshot;
        _regions = regions;
        _difference = diffs;
      }
    }

    ITextBuffer _buffer;
    ITextSnapshot _snapshot;
    List<TokenRegion> _regions;
    static object bufferTokenTaggerKey = new object();
    bool _disposed;

    internal IvyTokenTagger(ITextBuffer buffer) {
      _buffer = buffer;
      _snapshot = buffer.CurrentSnapshot;
      _regions = Scan(_snapshot);

      _buffer.Changed += new EventHandler<TextContentChangedEventArgs>(ReparseFile);
    }

    public void Dispose() {
      lock (this) {
        if (!_disposed) {
          _buffer.Changed -= ReparseFile;
          _buffer.Properties.RemoveProperty(bufferTokenTaggerKey);
          _buffer = null;
          _snapshot = null;
          _regions = null;
          _disposed = true;
        }
      }
      GC.SuppressFinalize(this);
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    public IEnumerable<ITagSpan<IvyTokenTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0)
        yield break;

      List<TokenRegion> currentRegions = _regions;
      ITextSnapshot currentSnapshot = _snapshot;

      // create a new SnapshotSpan for the entire region encompassed by the span collection
      SnapshotSpan entire = new SnapshotSpan(spans[0].Start, spans[spans.Count - 1].End).TranslateTo(currentSnapshot, SpanTrackingMode.EdgeExclusive);

      // return tags for any regions that fall within that span
      // BUGBUG: depending on how GetTags gets called (e.g., once for each line in the buffer), this may produce quadratic behavior
      foreach (var region in currentRegions) {
        if (entire.IntersectsWith(region.Span)) {
          yield return new TagSpan<IvyTokenTag>(new SnapshotSpan(region.Start, region.End), new IvyTokenTag(region.Kind));
        }
      }
    }

    /// <summary>
    /// Find all of the tag regions in the document (snapshot) and notify
    /// listeners of any that changed
    /// </summary>
    void ReparseFile(object sender, TextContentChangedEventArgs args) {
      ITextSnapshot snapshot = _buffer.CurrentSnapshot;
      if (snapshot == _snapshot)
        return;  // we've already computed the regions for this snapshot
      
      NormalizedSnapshotSpanCollection difference = new NormalizedSnapshotSpanCollection();
      ScanResult result;
      if (_buffer.Properties.TryGetProperty(bufferTokenTaggerKey, out result) &&
          (result._oldSnapshot == _snapshot) &&
          (result._newSnapshot == snapshot)) {
        difference = result._difference;
        // save the new baseline
        _regions = result._regions;
        _snapshot = snapshot;
      } else {
        List<TokenRegion>  regions = new List<TokenRegion>();
        List<SnapshotSpan> rescannedRegions = new List<SnapshotSpan>();

        // loop through the changes and check for changes in comments first. If 
        // the change is in a comments, we need to rescan starting from the 
        // beginning of the comments (which in multi-lined comments, it can
        // be a line that the changes are not on), otherwise, we can just rescan the lines
        // that the changes are on.
        bool done;
        SnapshotPoint start, end;
        for (int i = 0; i < args.Changes.Count; i++) {
          done = false;
          // get the span of the lines that the change is on.
          int cStart = args.Changes[i].NewSpan.Start;
          int cEnd = args.Changes[i].NewSpan.End;
          start = snapshot.GetLineFromPosition(cStart).Start;
          end = snapshot.GetLineFromPosition(cEnd).End;
          SnapshotSpan newSpan = new SnapshotSpan(start, end);
          foreach (TokenRegion r in _regions) {
            if (r.Kind == IvyTokenKind.Comment) {
              // if the change is in the comments, we want to start scanning from the
              // the beginning of the comments instead.
              SnapshotSpan span = r.Span.TranslateTo(snapshot, SpanTrackingMode.EdgeExclusive);
              if (span.IntersectsWith(newSpan)) {
                start = span.Start.Position < newSpan.Start.Position ? span.Start : newSpan.Start;
                end = span.End.Position > newSpan.End.Position ? span.End : newSpan.End;
                end = Scan(snapshot.GetText(new SnapshotSpan(start, end)), start, regions, snapshot);
                // record the regions that we rescanned.
                rescannedRegions.Add(new SnapshotSpan(start, end));
                done = true;
                break;
              }
            }
          }
          if (!done) {
            // scan the lines that the change is on to generate the new regions.
            end = Scan(snapshot.GetText(new SnapshotSpan(start, end)), start, regions, snapshot);
            // record the span that we rescanned.
            rescannedRegions.Add(new SnapshotSpan(start, end));
          }
        }

        List<SnapshotSpan> oldSpans = new List<SnapshotSpan>();
        List<SnapshotSpan> newSpans = new List<SnapshotSpan>();
        // record the newly created spans.
        foreach (TokenRegion r in regions) {
          newSpans.Add(r.Span);
        }
        // loop through the old scan results and remove the ones that 
        // are in the regions that are rescanned.
        foreach (TokenRegion r in _regions) {
          SnapshotSpan origSpan = r.Span.TranslateTo(snapshot, SpanTrackingMode.EdgeExclusive);
          bool obsolete = false;
          foreach (SnapshotSpan span in rescannedRegions) {
            if (origSpan.IntersectsWith(span)) {
              oldSpans.Add(span);
              obsolete = true;
              break;
            }
          }
          if (!obsolete) {
            TokenRegion region = new TokenRegion(origSpan.Start, origSpan.End, r.Kind);
            regions.Add(region);
          }
        }
        
        NormalizedSnapshotSpanCollection oldSpanCollection = new NormalizedSnapshotSpanCollection(oldSpans);
        NormalizedSnapshotSpanCollection newSpanCollection = new NormalizedSnapshotSpanCollection(newSpans);
        difference = SymmetricDifference(oldSpanCollection, newSpanCollection);

        // save the scan result
        _buffer.Properties[bufferTokenTaggerKey] = new ScanResult(_snapshot, snapshot, regions, difference);
        // save the new baseline
        _snapshot = snapshot;
        _regions = regions;
      }

      var chng = TagsChanged;
      if (chng != null) {
        foreach (var span in difference) {
          chng(this, new SnapshotSpanEventArgs(span));
        }
      }
    }

    static NormalizedSnapshotSpanCollection SymmetricDifference(NormalizedSnapshotSpanCollection first, NormalizedSnapshotSpanCollection second) {
      return NormalizedSnapshotSpanCollection.Union(
          NormalizedSnapshotSpanCollection.Difference(first, second),
          NormalizedSnapshotSpanCollection.Difference(second, first));
    }

    private static SnapshotPoint Scan(string txt, SnapshotPoint start, List<TokenRegion> newRegions, ITextSnapshot newSnapshot) {
      SnapshotPoint commentStart = new SnapshotPoint();
      int N = txt.Length;
      bool done = false;
      while (!done) {
        N = txt.Length;  // length of the current buffer
        int cur = 0;  // offset into the current buffer
        // repeatedly get the remaining tokens from this buffer
        int end;  // offset into the current buffer
        for (; ; cur = end) {
          // advance to the first character of a keyword or token
          IvyTokenKind ty = IvyTokenKind.Keyword;
          for (; ; cur++) {
            if (N <= cur) {
              // we've looked at everything in this buffer
              goto OUTER_CONTINUE;
            }
            char ch = txt[cur];
            if ('a' <= ch && ch <= 'z') break;
            if ('A' <= ch && ch <= 'Z') break;
            if ('0' <= ch && ch <= '9') { ty = IvyTokenKind.Number; break; }
            if (ch == '_' || ch == '?' || ch == '\\') break;  // parts of identifiers
            if (ch == '\"') { ty = IvyTokenKind.String; break; }
            if (ch == '#') { ty = IvyTokenKind.Comment; break; }
          }

          // advance to the end of the token
          end = cur + 1;  // offset into the current buffer

          if (ty == IvyTokenKind.Number) {
            // scan the rest of this number
            for (; end < N; end++) {
              char ch = txt[end];
              if ('0' <= ch && ch <= '9' || 'a' <= ch && ch <= 'z' || 'A' <= ch && ch <= 'Z' || ch == '_') {
              } else break;
            }
          } else if (ty == IvyTokenKind.String) {
            // scan the rest of this string, but not past the end-of-buffer
            for (; end < N; end++) {
              char ch = txt[end];
              if (ch == '\"') {
                end++; break;
              } else if (ch == '\\') {
                // escape sequence
                end++;
                if (end == N) { break; }
                ch = txt[end];
                if (ch == 'u') {
                  end += 4;
                  if (N <= end) { end = N; break; }
                }
              }
            }
          } else if (ty == IvyTokenKind.Comment) {
            if (end == N) continue;  // this was not the start of a comment; it was just a single "/" and we don't care to color it
            char ch = txt[end];
	    // a short comment, to the end of the line. (it's all we have)
            end = newSnapshot.GetLineFromPosition(start + end).End.Position - start;
          } else {
            int trailingDigits = 0;
            for (; end < N; end++) {
              char ch = txt[end];
              if ('a' <= ch && ch <= 'z') {
                trailingDigits = 0;
              } else if ('A' <= ch && ch <= 'Z') {
                trailingDigits = 0;
              } else if ('0' <= ch && ch <= '9') {
                trailingDigits++;
              } else if (ch == '_') {
                trailingDigits = 0;
              } else break;
            }
            // we have a keyword or an identifier
            string s = txt.Substring(cur, end - cur);
            {
              switch (s) {
                #region keywords


		case "relation":
		case "individual":
		case "function":
		case "axiom":
		case "conjecture":
		case "schema":
		case "instantiate":
		case "instance":
		case "derived":
		case "concept":
		case "init":
		case "action":
		case "method":
		case "state":
		case "assume":
		case "assert":
		case "set":
		case "null":
		case "old":
		case "from":
		case "update":
		case "params":
		case "in":
		case "match":
		case "ensures":
		case "requires":
		case "modifies":
		case "true":
		case "false":
		case "fresh":
		case "module":
		case "object":
		case "class":
		case "type":
		case "if":
		case "else":
		case "local":
		case "let":
		case "call":
		case "entry":
		case "macro":
		case "interpret":
		case "forall":
		case "exists":
		case "returns":
		case "mixin":
		case "execute":
		case "before":
		case "after":
		case "isolate":
		case "with":
		case "export":
		case "delegate":
		case "import":
		case "using":
		case "include":
		case "progress":
		case "rely":
		case "mixord":
		case "extract":
		case "destructor":
		case "some":
		case "maximizing":
		case "minimizing":
		case "private":
		case "implement":
		case "property":
		case "while":
		case "invariant":
		case "struct":
		case "definition":
		case "ghost":
		case "alias":
		case "trusted":
		case "this":
		case "var":
		case "attribute":
		case "variant":
		case "of":

                #endregion
                  break;
                #region keywords for built-in types
                case "bool":
                #endregion
                  ty = IvyTokenKind.BuiltInType;
                  break;
                default:
                  continue;  // it was an identifier, so we don't color it
              }
            }
          }
          newRegions.Add(new TokenRegion(new SnapshotPoint(newSnapshot, start + cur), new SnapshotPoint(newSnapshot, start + end), ty));
        }
      OUTER_CONTINUE:
        done = true;
      }
      return new SnapshotPoint(newSnapshot, start + N);
    }

    private List<TokenRegion> Scan(ITextSnapshot newSnapshot) {      
      List<TokenRegion> newRegions; 
      ScanResult result;
      if (_buffer.Properties.TryGetProperty(bufferTokenTaggerKey, out result) &&         
        result._newSnapshot == newSnapshot) {
        newRegions = result._regions;
      } else {
        newRegions = new List<TokenRegion>();
        int nextLineNumber = -1;
        foreach (ITextSnapshotLine line in newSnapshot.Lines) {
          if (line.LineNumber <= nextLineNumber) {
            // the line is already processed.
            continue;
          }
          string txt = line.GetText();  // the current line (without linebreak characters)
          SnapshotPoint end = Scan(txt, line.Start, newRegions, newSnapshot);
          nextLineNumber = newSnapshot.GetLineFromPosition(end).LineNumber;
        }
        _buffer.Properties[bufferTokenTaggerKey] = new ScanResult(null, newSnapshot, newRegions, null);
      }
      return newRegions;
    }

    
  }

  internal class TokenRegion
  {
    public SnapshotPoint Start { get; private set; }
    public SnapshotPoint End { get; private set; }
    public SnapshotSpan Span {
      get { return new SnapshotSpan(Start, End); }
    }
    public IvyTokenKind Kind { get; private set; }

    public TokenRegion(SnapshotPoint start, SnapshotPoint end, IvyTokenKind kind) {
      Start = start;
      End = end;
      Kind = kind;
    }
  }

  #endregion

}
