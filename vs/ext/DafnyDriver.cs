using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Ivy;
using Microsoft.VisualStudio.Text;
using Bpl = Microsoft.Boogie;
using Ivy = Microsoft.Ivy;


namespace IvyLanguage
{

  public class IvyDriver
  {
    readonly string _filename;
    readonly ITextSnapshot _snapshot;
    readonly ITextBuffer _buffer;
    Ivy.Program _program;
    static object bufferIvyKey = new object();

    List<IvyError> _errors = new List<IvyError>();
    public List<IvyError> Errors { get { return _errors; } }

    public IvyDriver(ITextBuffer buffer, string filename) {
      _buffer = buffer;
      _snapshot = buffer.CurrentSnapshot;
      _filename = filename;
    }

    static IvyDriver() {
      // TODO(wuestholz): Do we really need to initialze this here?
      Initialize();
    }

    static void Initialize() {
      if (Ivy.IvyOptions.O == null) {
        var options = new Ivy.IvyOptions();
        options.ProverKillTime = 10;
        options.AutoTriggers = true;
        options.ErrorTrace = 0;
        options.VcsCores = Math.Max(1, System.Environment.ProcessorCount - 1);
        options.ModelViewFile = "-";
        options.UnicodeOutput = true;
        Ivy.IvyOptions.Install(options);

        // Read additional options from IvyOptions.txt
        string codebase = Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location);
        string optionsFilePath = Path.Combine(codebase, "IvyOptions.txt");
        if (File.Exists(optionsFilePath)) {
          var optionsReader = new StreamReader(new FileStream(optionsFilePath, FileMode.Open, FileAccess.Read));
          List<string> args = new List<string>();
          while (true) {
            string line = optionsReader.ReadLine();
            if (line == null) break;
            line = line.Trim();
            if (line.Length == 0 || line.StartsWith("//")) continue;
            args.Add(line);
          }
          optionsReader.Close();
          CommandLineOptions.Clo.Parse(args.ToArray());
        } else {
          options.ApplyDefaultOptions();
        }

        ExecutionEngine.printer = new DummyPrinter();
        ExecutionEngine.errorInformationFactory = new IvyErrorInformationFactory();
        ChangeIncrementalVerification(2);
      }
    }


    #region Output

    class DummyPrinter : OutputPrinter
    {
      public void AdvisoryWriteLine(string format, params object[] args)
      {
      }

      public void ErrorWriteLine(TextWriter tw, string format, params object[] args)
      {
      }

      public void ErrorWriteLine(TextWriter tw, string s)
      {
      }

      public void Inform(string s, TextWriter tw)
      {
      }

      public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null)
      {
      }

      public void WriteTrailer(PipelineStatistics stats)
      {
      }

      public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true)
      {
      }
    }

    #endregion

    #region Parsing and type checking

    internal Ivy.Program ProcessResolution(bool runResolver) {
      if (!ParseAndTypeCheck(runResolver)) {
        return null;
      }
      return _program;
    }

    bool ParseAndTypeCheck(bool runResolver) {
      Tuple<ITextSnapshot, Ivy.Program, List<IvyError>> parseResult;
      Ivy.Program program;
      var errorReporter = new VSErrorReporter(this);
      if (_buffer.Properties.TryGetProperty(bufferIvyKey, out parseResult) &&
         (parseResult.Item1 == _snapshot)) {
        // already parsed;
        program = parseResult.Item2;
        _errors = parseResult.Item3;
        if (program == null)
          runResolver = false;
      } else {
        Ivy.ModuleDecl module = new Ivy.LiteralModuleDecl(new Ivy.DefaultModuleDecl(), null);
        Ivy.BuiltIns builtIns = new Ivy.BuiltIns();
        var parseErrors = new Ivy.Errors(errorReporter);
        int errorCount = Ivy.Parser.Parse(_snapshot.GetText(), _filename, _filename, null, module, builtIns, parseErrors);
        string errString = Ivy.Main.ParseIncludes(module, builtIns, new List<string>(), parseErrors);

        if (errorCount != 0 || errString != null) {
          runResolver = false;
          program = null;
        } else {
          program = new Ivy.Program(_filename, module, builtIns, errorReporter);
        }
        _buffer.Properties[bufferIvyKey] = new Tuple<ITextSnapshot, Ivy.Program, List<IvyError>>(_snapshot, program, _errors);
      }
      if (!runResolver) {
        return false;
      }

      var r = new Resolver(program);
      r.ResolveProgram(program);
      if (errorReporter.Count(ErrorLevel.Error) != 0)
        return false;

      _program = program;
      return true;  // success
    }


    void RecordError(string filename, int line, int col, ErrorCategory cat, string msg, bool isRecycled = false)
    {
      _errors.Add(new IvyError(filename, line - 1, col - 1, cat, msg, _snapshot, isRecycled, null, System.IO.Path.GetFullPath(this._filename) == filename));
    }

    class VSErrorReporter : Ivy.ErrorReporter
    {
      IvyDriver dd;

      public VSErrorReporter(IvyDriver dd) {
        this.dd = dd;
      }

      // TODO: The error tracking could be made better to track the full information returned by Ivy
      public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
        if (base.Message(source, level, tok, msg)) {
          switch (level) {
            case ErrorLevel.Error:
              dd.RecordError(tok.filename, tok.line, tok.col, source == MessageSource.Parser ? ErrorCategory.ParseError : ErrorCategory.ResolveError, msg);
              break;
            case ErrorLevel.Warning:
              dd.RecordError(tok.filename, tok.line, tok.col, source == MessageSource.Parser ? ErrorCategory.ParseWarning : ErrorCategory.ResolveWarning, msg);
              break;
            case ErrorLevel.Info:
              // The AllMessages variable already keeps track of this
              break;
          }
          return true;
        } else {
          return false;
        }
      }
    }

    public class ErrorSink : Bpl.IErrorSink
    {
      IvyDriver dd;

      public ErrorSink(IvyDriver dd) {
        this.dd = dd;
      }
      public void Error(Bpl.IToken tok, string msg) {
        dd.RecordError(tok.filename, tok.line, tok.col, ErrorCategory.VerificationError, msg);
      }
    }

    #endregion

    #region Compilation

    public static void Compile(Ivy.Program ivyProgram, TextWriter outputWriter)
    {
      Microsoft.Ivy.IvyOptions.O.SpillTargetCode = true;
      // Currently there are no provisions for specifying other files to compile with from the 
      // VS interface, so just send an empty list.
      ReadOnlyCollection<string> otherFileNames = new List<string>().AsReadOnly();
      Microsoft.Ivy.IvyDriver.CompileIvyProgram(ivyProgram, ivyProgram.FullName, otherFileNames, outputWriter);
    }

    #endregion

    #region Boogie interaction

    class IvyErrorInformationFactory : ErrorInformationFactory
    {
      public override ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId, string originalRequestId, string category = null)
      {
        return new IvyErrorInformation(tok, msg, requestId, originalRequestId, category);
      }
    }

    class IvyErrorInformation : ErrorInformation
    {
      public IvyErrorInformation(IToken tok, string msg, string requestId, string originalRequestId, string category = null)
        : base(tok, msg)
      {
        RequestId = requestId;
        OriginalRequestId = originalRequestId;
        Category = category;
        AddNestingsAsAux(tok);
      }

      public override void AddAuxInfo(IToken tok, string msg, string category = null)
      {
        base.AddAuxInfo(tok, msg, category);
        AddNestingsAsAux(tok);
      }

      void AddNestingsAsAux(IToken tok)
      {
        while (tok != null && tok is Ivy.NestedToken)
        {
          var nt = (Ivy.NestedToken)tok;
          tok = nt.Inner;
          Aux.Add(new AuxErrorInfo(tok, "Related location"));
        }
      }
    }

    public static int IncrementalVerificationMode()
    {
      return Ivy.IvyOptions.Clo.VerifySnapshots;
    }

    public static void SetDiagnoseTimeouts(bool v)
    {
      Ivy.IvyOptions.Clo.RunDiagnosticsOnTimeout = v;
    }

    public static int ChangeIncrementalVerification(int mode)
    {
      var old = Ivy.IvyOptions.Clo.VerifySnapshots;
      if (mode == 1 && 1 <= old)
      {
        // Disable mode 1.
        Ivy.IvyOptions.Clo.VerifySnapshots = 0;
      }
      else if (mode == 2 && old == 2)
      {
        // Disable mode 2.
        Ivy.IvyOptions.Clo.VerifySnapshots = 1;
      }
      else
      {
        // Enable mode.
        Ivy.IvyOptions.Clo.VerifySnapshots = mode;
      }
      return Ivy.IvyOptions.Clo.VerifySnapshots;
    }

    public static bool ChangeAutomaticInduction() {
      var old = Ivy.IvyOptions.O.Induction;
      // toggle between modes 1 and 3
      Ivy.IvyOptions.O.Induction = old == 1 ? 3 : 1;
      return Ivy.IvyOptions.O.Induction == 3;
    }

    public bool Verify(Ivy.Program ivyProgram, ResolverTagger resolver, string uniqueIdPrefix, string requestId, ErrorReporterDelegate er) {

      Ivy.Translator translator = new Ivy.Translator(ivyProgram.reporter);
      var translatorFlags = new Ivy.Translator.TranslatorFlags() { InsertChecksums = true, UniqueIdPrefix = uniqueIdPrefix };


      var boogiePrograms = Ivy.Translator.Translate(ivyProgram, ivyProgram.reporter, translatorFlags);

      var impls = boogiePrograms.SelectMany(p => p.Item2.Implementations);
      resolver.ReInitializeVerificationErrors(requestId, impls);

      bool success = false;
      var errorSink = new ErrorSink(this);
      
      foreach (var kv in boogiePrograms) {
        var boogieProgram = kv.Item2;

        // TODO(wuestholz): Maybe we should use a fixed program ID to limit the memory overhead due to the program cache in Boogie.
        PipelineOutcome oc = BoogiePipeline(boogieProgram, 1 < Ivy.DafnyOptions.Clo.VerifySnapshots ? uniqueIdPrefix : null, requestId, errorSink, er);
        switch (oc) {
          case PipelineOutcome.Done:
          case PipelineOutcome.VerificationCompleted:
            // TODO:  This would be the place to proceed to compile the program, if desired
            success = true;
            break;
          case PipelineOutcome.FatalError:
          default:
            return false;
        }
      }
      return success;
    }

    /// <summary>
    /// Resolve, type check, infer invariants for, and verify the given Boogie program.
    /// The intention is that this Boogie program has been produced by translation from something
    /// else.  Hence, any resolution errors and type checking errors are due to errors in
    /// the translation.
    /// </summary>
    static PipelineOutcome BoogiePipeline(Bpl.Program/*!*/ program, string programId, string requestId, ErrorSink errorSink, ErrorReporterDelegate er)
    {
      Contract.Requires(program != null);

      PipelineOutcome oc = BoogieResolveAndTypecheck(program, errorSink);
      if (oc == PipelineOutcome.ResolvedAndTypeChecked) {
        ExecutionEngine.EliminateDeadVariables(program);
        ExecutionEngine.CollectModSets(program);
        ExecutionEngine.CoalesceBlocks(program);
        ExecutionEngine.Inline(program);
        return ExecutionEngine.InferAndVerify(program, new PipelineStatistics(), programId, er, requestId);
      }
      return oc;
    }

    /// <summary>
    /// Resolves and type checks the given Boogie program.
    /// Returns:
    ///  - Done if no errors occurred, and command line specified no resolution or no type checking.
    ///  - ResolutionError if a resolution error occurred
    ///  - TypeCheckingError if a type checking error occurred
    ///  - ResolvedAndTypeChecked if both resolution and type checking succeeded
    /// </summary>
    static PipelineOutcome BoogieResolveAndTypecheck(Bpl.Program program, ErrorSink errorSink) {
      Contract.Requires(program != null);
      // ---------- Resolve ------------------------------------------------------------
      int errorCount = program.Resolve(errorSink);
      if (errorCount != 0) {
        return PipelineOutcome.ResolutionError;
      }

      // ---------- Type check ------------------------------------------------------------
      errorCount = program.Typecheck(errorSink);
      if (errorCount != 0) {
        return PipelineOutcome.TypeCheckingError;
      }

      return PipelineOutcome.ResolvedAndTypeChecked;
    }

    #endregion
  }

}
