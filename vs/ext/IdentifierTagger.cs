using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Diagnostics.Contracts;
using Microsoft.Ivy;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;
using Bpl = Microsoft.Boogie;

namespace IvyLanguage
{

  #region Provider

  [Export(typeof(ITaggerProvider))]
  [ContentType("ivy")]
  [TagType(typeof(IvyTokenTag))]
  internal sealed class IdentifierTaggerProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<IIvyResolverTag> tagAggregator = AggregatorFactory.CreateTagAggregator<IIvyResolverTag>(buffer);
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new IdentifierTagger(buffer, tagAggregator) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  #endregion


  #region Tagger

  /// <summary>
  /// Translate IvyResolverTag's into IOutliningRegionTag's
  /// </summary>
  internal sealed class IdentifierTagger : ITagger<IvyTokenTag>
  {
    ITextBuffer _buffer;
    ITextSnapshot _snapshot;  // the most recent snapshot of _buffer that we have been informed about
    Microsoft.Ivy.Program _program;  // the program parsed from _snapshot
    List<IdRegion> _regions = new List<IdRegion>();  // the regions generated from _program
    public Dictionary<SnapshotSpan, Bpl.IToken> _definitions = new Dictionary<SnapshotSpan, Bpl.IToken>();
    ITagAggregator<IIvyResolverTag> _aggregator;

    public static readonly IDictionary<ITextBuffer, IdentifierTagger> IdentifierTaggers = new Dictionary<ITextBuffer, IdentifierTagger>();


    internal IdentifierTagger(ITextBuffer buffer, ITagAggregator<IIvyResolverTag> tagAggregator) {
      _buffer = buffer;
      _snapshot = _buffer.CurrentSnapshot;
      _aggregator = tagAggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
      IdentifierTaggers[_buffer] = this;
    }

    /// <summary>
    /// Find the Error tokens in the set of all tokens and create an ErrorTag for each
    /// </summary>
    public IEnumerable<ITagSpan<IvyTokenTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      // (A NormalizedSnapshotSpanCollection contains spans that all come from the same snapshot.)
      // The spans are ordered by the .Start component, and the collection contains no adjacent or abutting spans.
      // Hence, to find a span that includes all the ones in "spans", we only need to look at the .Start for the
      // first spand and the .End of the last span:
      var startPoint = spans[0].Start;
      var endPoint = spans[spans.Count - 1].End;

      // Note, (startPoint,endPoint) are points in the spans for which we're being asked to provide tags.  We need to translate
      // these back into the most recent snapshot that we've computed regions for, namely _snapshot.
      var entire = new SnapshotSpan(startPoint, endPoint).TranslateTo(_snapshot, SpanTrackingMode.EdgeExclusive);
      int start = entire.Start;
      int end = entire.End;
      foreach (var r in _regions) {
        if (0 <= r.Length && r.Start <= end && start <= r.Start + r.Length) {
          IvyTokenKind kind;
          switch (r.Kind) {
            case IdRegion.OccurrenceKind.Use:
              kind = IvyTokenKind.VariableIdentifier; break;
            case IdRegion.OccurrenceKind.Definition:
              kind = IvyTokenKind.VariableIdentifierDefinition; break;
            case IdRegion.OccurrenceKind.WildDefinition:
              kind = IvyTokenKind.Keyword; break;
            case IdRegion.OccurrenceKind.AdditionalInformation:
              kind = IvyTokenKind.AdditionalInformation; break;
            case IdRegion.OccurrenceKind.Attribute:
              kind = IvyTokenKind.Attribute; break;
            case IdRegion.OccurrenceKind.RecognizedAttributeId:
              kind = IvyTokenKind.RecognizedAttributeId; break;
            default:
              Contract.Assert(false);  // unexpected OccurrenceKind
              goto case IdRegion.OccurrenceKind.Use;  // to please compiler
          }
          yield return new TagSpan<IvyTokenTag>(
            new SnapshotSpan(_snapshot, r.Start, r.Length),
            new IvyTokenTag(kind, r.HoverText, r.Variable));
        }
      }
    }

    // the Classifier tagger is translating buffer change events into TagsChanged events, so we don't have to
    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
      var r = sender as ResolverTagger;
      if (r != null) {
        ITextSnapshot snap;
        Microsoft.Ivy.Program prog;
        lock (this) {
          snap = r.Snapshot;
          prog = r.Program;
        }
        if (prog != null) {
          if (!ComputeIdentifierRegions(prog, snap))
            return;  // no new regions

          var chng = TagsChanged;
          if (chng != null) {
            NormalizedSnapshotSpanCollection spans = e.Span.GetSpans(_buffer.CurrentSnapshot);
            if (spans.Count > 0) {
              SnapshotSpan span = new SnapshotSpan(spans[0].Start, spans[spans.Count - 1].End);
              chng(this, new SnapshotSpanEventArgs(span));
            }
          }
        }
      }
    }

    bool ComputeIdentifierRegions(Microsoft.Ivy.Program program, ITextSnapshot snapshot) {
      Contract.Requires(snapshot != null);

      if (program == _program)
        return false;  // no new regions

      _snapshot = snapshot;
      List<IdRegion> newRegions = new List<IdRegion>();

      foreach (var info in program.reporter.AllMessages[ErrorLevel.Info]) {
        IdRegion.Add(newRegions, program, info.token, info.message, info.token.val.Length);
      }

      foreach (var module in program.Modules()) {
        if (module.IsFacade) {
          continue;
        }
        foreach (var d in module.TopLevelDecls) {
          IdRegion.AddRecognizedAttributes(d.Attributes, newRegions, program);
          if (d is DatatypeDecl) {
            var dt = (DatatypeDecl)d;
            foreach (var ctor in dt.Ctors) {
              foreach (var dtor in ctor.Destructors) {
                if (dtor.CorrespondingFormal.HasName) {
                  IdRegion.Add(newRegions, program, dtor.tok, dtor, null, "destructor", true, module);
                }
              }
            }
          } else if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
            foreach (var p in iter.Ins) {
              IdRegion.Add(newRegions, program, p.tok, p, true, iter, module);
            }
            foreach (var p in iter.Outs) {
              IdRegion.Add(newRegions, program, p.tok, p, true, "yield-parameter", iter, module);
            }
            iter.Reads.Expressions.ForEach(fe => FrameExprRegions(fe, newRegions, true, program, module));
            iter.Modifies.Expressions.ForEach(fe => FrameExprRegions(fe, newRegions, true, program, module));
            iter.Requires.ForEach(e => ExprRegions(e.E, newRegions, program, module));
            iter.YieldRequires.ForEach(e => ExprRegions(e.E, newRegions, program, module));
            iter.YieldEnsures.ForEach(e => ExprRegions(e.E, newRegions, program, module));
            iter.Ensures.ForEach(e => ExprRegions(e.E, newRegions, program, module));
            if (!((ICallable)iter).InferredDecreases) {
              iter.Decreases.Expressions.ForEach(e => ExprRegions(e, newRegions, program, module));
            }
            if (iter.Body != null) {
              StatementRegions(iter.Body, newRegions, program, module);
            }

          } else if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            foreach (var member in cl.Members) {
              IdRegion.AddRecognizedAttributes(member.Attributes, newRegions, program);
              if (Attributes.Contains(member.Attributes, "auto_generated")) {
                // do nothing
              } else  if (member is Function) {
                var f = (Function)member;
                foreach (var p in f.Formals) {
                  IdRegion.Add(newRegions, program, p.tok, p, true, f, module);
                }
                f.Req.ForEach(e => ExprRegions(e, newRegions, program, module));
                f.Reads.ForEach(fe => FrameExprRegions(fe, newRegions, true, program, module));
                f.Ens.ForEach(e => ExprRegions(e, newRegions, program, module));
                f.Decreases.Expressions.ForEach(e => ExprRegions(e, newRegions, program, module));
                if (f.Body != null) {
                  ExprRegions(f.Body, newRegions, program, module);
                }
              } else if (member is Method) {
                var m = (Method)member;
                foreach (var p in m.Ins) {
                  IdRegion.Add(newRegions, program, p.tok, p, true, m, module);
                }
                foreach (var p in m.Outs) {
                  IdRegion.Add(newRegions, program, p.tok, p, true, m, module);
                }
                m.Req.ForEach(e => ExprRegions(e.E, newRegions, program, module));
                m.Mod.Expressions.ForEach(fe => FrameExprRegions(fe, newRegions, true, program, module));
                m.Ens.ForEach(e => ExprRegions(e.E, newRegions, program, module));
                m.Decreases.Expressions.ForEach(e => ExprRegions(e, newRegions, program, module));
                if (m.Body != null) {
                  StatementRegions(m.Body, newRegions, program, module);
                }
              } else if (member is SpecialField) {
                // do nothing
              } else if (member is Field) {
                var fld = (Field)member;
                IdRegion.Add(newRegions, program, fld.tok, fld, null, "field", true, module);
              }
            }
          } else if (d is NewtypeDecl) {
            var dd = (NewtypeDecl)d;
            if (dd.Var != null) {
              IdRegion.Add(newRegions, program, dd.Var.tok, dd.Var, true, (ICallable)null, module);
              ExprRegions(dd.Constraint, newRegions, program, module);
            }
          }
        }
      }
      _regions = newRegions;
      _program = program;
      return true;
    }

    void FrameExprRegions(FrameExpression fe, List<IdRegion> regions, bool descendIntoExpressions, Microsoft.Ivy.Program prog, ModuleDefinition module) {
      Contract.Requires(fe != null);
      Contract.Requires(regions != null);
      Contract.Requires(prog != null);
      if (descendIntoExpressions) {
        ExprRegions(fe.E, regions, prog, module);
      }
      if (fe.Field != null) {
        Microsoft.Ivy.Type showType = null;  // TODO: if we had the instantiated type of this field, that would have been nice to use here (but the Resolver currently does not compute or store the instantiated type for a FrameExpression)
        IdRegion.Add(regions, prog, fe.tok, fe.Field, showType, "field", false, module);
        RecordUseAndDef(prog, fe.tok, fe.Field.Name.Length, fe.Field.tok);
      }
    }

    void ExprRegions(Microsoft.Ivy.Expression expr, List<IdRegion> regions, Microsoft.Ivy.Program prog, ModuleDefinition module) {
      Contract.Requires(expr != null);
      Contract.Requires(regions != null);
      Contract.Requires(prog != null);
      if (expr is AutoGeneratedExpression) {
        // do nothing
        return;
      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        IdRegion.Add(regions, prog, e.tok, e.Var, false, (ICallable)null, module);
      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        var field = e.Member as Field;
        if (field != null) {
          IdRegion.Add(regions, prog, e.tok, field, e.Type, "field", false, module);
        }
        if (e.Member != null) {
          RecordUseAndDef(prog, e.tok, e.Member.Name.Length, e.Member.tok);
        }
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        var func = e.Function;
        if (func != null) {
          RecordUseAndDef(prog, e.tok, func.Name.Length, func.tok);
        }
      } else if (expr is ApplySuffix) {
         // No need to call ExprRegions on the Lhs field because the for loop at the end of this function will do that.
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        IdRegion.AddRecognizedAttributes(e.Attributes, regions, prog);
        foreach (var bv in e.BoundVars) {
          IdRegion.Add(regions, prog, bv.tok, bv, true, (ICallable)null, module);
        }
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        IdRegion.AddRecognizedAttributes(e.Attributes, regions, prog);
        foreach (var bv in e.BoundVars) {
          IdRegion.Add(regions, prog, bv.tok, bv, true, (ICallable)null, module);
        }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        foreach (var kase in e.Cases) {
          kase.Arguments.ForEach(bv => {
            IdRegion.Add(regions, prog, bv.tok, bv, true, (ICallable)null, module);
            // if the arguments is an encapsulation of different boundvars from nested match cases,
            // add the boundvars so that they can show up in the IDE correctly
            if (bv.tok is MatchCaseToken) {
              MatchCaseToken mt = (MatchCaseToken)bv.tok;
              foreach(Tuple<Bpl.IToken, BoundVar, bool> entry in mt.varList) {
                IdRegion.Add(regions, prog, entry.Item1, entry.Item2, entry.Item3, (ICallable)null, module);
              }
            }
          });
        }
      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        // Do the subexpressions only once (that is, avoid the duplication that occurs in the desugared form of the ChainingExpression)
        e.Operands.ForEach(ee => ExprRegions(ee, regions, prog, module));
        return;  // return here, so as to avoid doing the subexpressions below
      }
      foreach (var ee in expr.SubExpressions) {
        ExprRegions(ee, regions, prog, module);
      }
    }

    void RecordUseAndDef(Program prog, Bpl.IToken useTok, int length, Bpl.IToken defTok) {
      if (prog.FullName.ToLower().CompareTo(useTok.filename.ToLower()) == 0) {  // Otherwise, we're looking at an included file
        // add to the definition table so we know where the definition for this expr is
        SnapshotSpan span = new SnapshotSpan(this._snapshot, useTok.pos, length);
        if (!_definitions.ContainsKey(span)) {
          _definitions.Add(span, defTok);
        }
      }
    }

    public bool FindDefinition(int caretPos, out string fileName, out int lineNumber, out int offset) {
      foreach (var use in _definitions.Keys) {
        if (caretPos >= use.Start && caretPos <= use.End) {
          // go to the source
          Bpl.IToken tok;
          if (_definitions.TryGetValue(use, out tok)) {
            fileName = tok.filename;
            lineNumber = tok.line - 1;
            offset = tok.col - 1;
            return true;
          }
        }
      }
      fileName = null;
      lineNumber = offset = 0;
      return false;
    }

    void StatementRegions(Statement stmt, List<IdRegion> regions, Microsoft.Ivy.Program prog, ModuleDefinition module) {
      Contract.Requires(stmt != null);
      Contract.Requires(regions != null);
      Contract.Requires(prog != null);
      IdRegion.AddRecognizedAttributes(stmt.Attributes, regions, prog);
      if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        // Add the variables here, once, and then go directly to the RHS's (without letting the sub-statements re-do the LHS's)
        foreach (var local in s.Locals) {
          IdRegion.AddRecognizedAttributes(local.Attributes, regions, prog);
          IdRegion.Add(regions, prog, local.Tok, local, true, (ICallable)null, module);
        }
        if (s.Update == null) {
          // the VarDeclStmt has no associated assignment
        } else if (s.Update is UpdateStmt) {
          var upd = (UpdateStmt)s.Update;
          foreach (var rhs in upd.Rhss) {
            foreach (var ee in rhs.SubExpressions) {
              ExprRegions(ee, regions, prog, module);
            }
            if (rhs is TypeRhs) {
              CallStmt call = ((TypeRhs)rhs).InitCall;
              if (call != null) {
                var method = call.Method;
                if (method != null) {
                  if (method is Constructor) {
                    // call token starts at the beginning of "new C()", so we need to add 4 to the length.
                    RecordUseAndDef(prog, call.Tok, method.EnclosingClass.Name.Length+4, method.EnclosingClass.tok);
                  } else {
                    RecordUseAndDef(prog, call.Tok, method.Name.Length, method.tok);
                  }
                }
              }
            }
          }
        } else {
          var upd = (AssignSuchThatStmt)s.Update;
          ExprRegions(upd.Expr, regions, prog, module);
        }
        // we're done, so don't do the sub-statements/expressions again
        return;
      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        s.BoundVars.ForEach(bv => IdRegion.Add(regions, prog, bv.tok, bv, true, (ICallable)null, module));
      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        foreach (var kase in s.Cases) {
          kase.Arguments.ForEach(bv => {
            IdRegion.Add(regions, prog, bv.tok, bv, true, (ICallable)null, module);
            // if the arguments is an encapsulation of different boundvars from nested match cases,
            // add the boundvars so that they can show up in the IDE correctly
            if (bv.tok is MatchCaseToken) {
              MatchCaseToken mt = (MatchCaseToken)bv.tok;
              foreach (Tuple<Bpl.IToken, BoundVar, bool> entry in mt.varList) {
                IdRegion.Add(regions, prog, entry.Item1, entry.Item2, entry.Item3, (ICallable)null, module);
              }
            }              
          });
        }
      } else if (stmt is LoopStmt) {
        var s = (LoopStmt)stmt;
        if (s.Mod.Expressions != null) {
          s.Mod.Expressions.ForEach(fe => FrameExprRegions(fe, regions, false, prog, module));
        }
      } else if (stmt is CalcStmt) {
        var s = (CalcStmt)stmt;
        // skip the last line, which is just a duplicate anyway
        for (int i = 0; i < s.Lines.Count - 1; i++) {
          ExprRegions(s.Lines[i], regions, prog, module);
        }
        foreach (var ss in stmt.SubStatements) {
          StatementRegions(ss, regions, prog, module);
        }
        return;
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        var method = s.Method;
        if (method != null) {
          RecordUseAndDef(prog, s.MethodSelect.tok, method.Name.Length, method.tok);
        }
      }
      foreach (var ee in stmt.SubExpressions) {
        ExprRegions(ee, regions, prog, module);
      }
      foreach (var ss in stmt.SubStatements) {
        StatementRegions(ss, regions, prog, module);
      }
    }

    class IdRegion : IvyRegion
    {
      public readonly int Start;
      public readonly int Length;
      public readonly string HoverText;
      public enum OccurrenceKind { Use, Definition, WildDefinition, AdditionalInformation, Attribute, RecognizedAttributeId }
      public readonly OccurrenceKind Kind;
      public readonly IVariable Variable;

      public static void Add(List<IdRegion> regions, Microsoft.Ivy.Program prog, Bpl.IToken tok, IVariable v, bool isDefinition, ICallable callableContext, ModuleDefinition context) {
        Contract.Requires(regions != null);
        Contract.Requires(prog != null);
        Contract.Requires(tok != null);
        Contract.Requires(v != null);
        Add(regions, prog, tok, v, isDefinition, null, callableContext, context);
      }
      public static void Add(List<IdRegion> regions, Microsoft.Ivy.Program prog, Bpl.IToken tok, IVariable v, bool isDefinition, string kind, ICallable callableContext, ModuleDefinition context) {
        Contract.Requires(regions != null);
        Contract.Requires(prog != null);
        Contract.Requires(tok != null);
        Contract.Requires(v != null);
        if (InMainFileAndUserDefined(prog, tok)) {
          regions.Add(new IdRegion(tok, v, isDefinition, kind, callableContext, context));
        }
      }
      public static void Add(List<IdRegion> regions, Microsoft.Ivy.Program prog, Bpl.IToken tok, Field decl, Microsoft.Ivy.Type showType, string kind, bool isDefinition, ModuleDefinition context) {
        Contract.Requires(regions != null);
        Contract.Requires(prog != null);
        Contract.Requires(tok != null);
        Contract.Requires(decl != null);
        Contract.Requires(kind != null);
        if (InMainFileAndUserDefined(prog, tok)) {
          regions.Add(new IdRegion(tok, decl, showType, kind, isDefinition, context));
        }
      }

      public static void Add(List<IdRegion> regions, Microsoft.Ivy.Program prog, Bpl.IToken tok, string text, int length) {
        Contract.Requires(regions != null);
        Contract.Requires(prog != null);
        Contract.Requires(tok != null);
        Contract.Requires(text != null);
        if (InMainFileAndUserDefined(prog, tok)) {
          regions.Add(new IdRegion(tok, OccurrenceKind.AdditionalInformation, text, length));
        }
      }

      public static void AddRecognizedAttributes(Attributes attrs, List<IdRegion> regions, Microsoft.Ivy.Program prog) {
        Contract.Requires(regions != null);
        Contract.Requires(prog != null);
        foreach (var a in attrs.AsEnumerable()) {
          var usa = a as UserSuppliedAttributes;
          if (usa != null && InMainFileAndUserDefined(prog, usa.tok)) {
            regions.Add(new IdRegion(usa.OpenBrace, usa.CloseBrace, OccurrenceKind.Attribute));
            if (usa.Recognized) {
              if (usa.Colon.pos + usa.Colon.val.Length == usa.tok.pos) {
                // just do one highlight
                regions.Add(new IdRegion(usa.Colon, OccurrenceKind.RecognizedAttributeId, null, usa.Colon.val.Length + usa.tok.val.Length));
              } else {
                regions.Add(new IdRegion(usa.Colon, OccurrenceKind.RecognizedAttributeId, null, usa.Colon.val.Length));
                regions.Add(new IdRegion(usa.tok, OccurrenceKind.RecognizedAttributeId, null, usa.tok.val.Length));
              }
            }
          }
        }
      }

      private IdRegion(Bpl.IToken tok, IVariable v, bool isDefinition, string kind, ICallable callableContext, ModuleDefinition context) {
        Contract.Requires(tok != null);
        Contract.Requires(v != null);
        Start = tok.pos;
        Length = v.DisplayName.Length;
        if (kind == null) {
          // use default
          if (v is LocalVariable) {
            kind = "local variable";
          } else if (v is BoundVar) {
            kind = "bound variable";
          } else {
            var formal = (Formal)v;
            kind = formal.InParam ? "in-parameter" : "out-parameter";
            if (callableContext is TwoStateLemma && !formal.IsOld) {
              kind = "new " + kind;
            }
            if (formal is ImplicitFormal) {
              kind = "implicit " + kind;
            }
          }
        }
        Variable = v;
        HoverText = string.Format("({2}{3}) {0}: {1}", v.DisplayName, v.Type.TypeName(context), v.IsGhost ? "ghost " : "", kind);
        Kind = !isDefinition ? OccurrenceKind.Use : LocalVariable.HasWildcardName(v) ? OccurrenceKind.WildDefinition : OccurrenceKind.Definition;
      }
      private IdRegion(Bpl.IToken tok, Field decl, Microsoft.Ivy.Type showType, string kind, bool isDefinition, ModuleDefinition context) {
        Contract.Requires(tok != null);
        Contract.Requires(decl != null);
        Contract.Requires(kind != null);
        if (showType == null) {
          showType = decl.Type;
        }
        Start = tok.pos;
        Length = decl.Name.Length;
        HoverText = string.Format("({4}{2}{3}) {0}: {1}", decl.FullNameInContext(context), showType.TypeName(context),
          decl.IsGhost ? "ghost " : "",
          kind,
          decl.IsUserMutable || decl is DatatypeDestructor ? "" : decl.IsMutable ? " non-assignable " : "immutable ");
        Kind = !isDefinition ? OccurrenceKind.Use : OccurrenceKind.Definition;
      }

      private IdRegion(Bpl.IToken tok, OccurrenceKind occurrenceKind, string info, int length)
      {
        this.Start = tok.pos;
        this.Length = length;
        this.Kind = occurrenceKind;
        this.HoverText = info;
      }

      /// <summary>
      /// The following constructor is suitable for recognized attributes.
      /// </summary>
      private IdRegion(Bpl.IToken from, Bpl.IToken thru, OccurrenceKind occurrenceKind) {
        this.Start = from.pos;
        this.Length = thru.pos + thru.val.Length - from.pos;
        this.Kind = occurrenceKind;
        this.HoverText = null;
      }
    }
  }

  public abstract class IvyRegion
  {
    public static bool InMainFileAndUserDefined(Microsoft.Ivy.Program prog, Bpl.IToken tok) {
      Contract.Requires(prog != null);
      Contract.Requires(tok != null);
      return object.Equals(prog.FullName, tok.filename) && !(tok is AutoGeneratedToken);
    }
  }

  #endregion
}
