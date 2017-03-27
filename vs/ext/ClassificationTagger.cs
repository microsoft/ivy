using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Windows.Media;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Classification;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;


namespace IvyLanguage
{

  #region Provider

  [Export(typeof(ITaggerProvider))]
  [ContentType("ivy")]
  [TagType(typeof(ClassificationTag))]
  internal sealed class IvyClassifierProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    [Import]
    internal IClassificationTypeRegistryService ClassificationTypeRegistry = null;

    [Import]
    internal Microsoft.VisualStudio.Language.StandardClassification.IStandardClassificationService Standards = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<IvyTokenTag> tagAggregator = AggregatorFactory.CreateTagAggregator<IvyTokenTag>(buffer);
      return new IvyClassifier(buffer, tagAggregator, ClassificationTypeRegistry, Standards) as ITagger<T>;
    }
  }

  #endregion

  #region Tagger

  internal sealed class IvyClassifier : ITagger<ClassificationTag>
  {
    ITextBuffer _buffer;
    ITagAggregator<IvyTokenTag> _aggregator;
    IDictionary<IvyTokenKind, IClassificationType> _typeMap;

    

    internal IvyClassifier(ITextBuffer buffer,
                             ITagAggregator<IvyTokenTag> tagAggregator,
                             IClassificationTypeRegistryService typeService, Microsoft.VisualStudio.Language.StandardClassification.IStandardClassificationService standards) {
      _buffer = buffer;
      _aggregator = tagAggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);

      // use built-in classification types:
      _typeMap = new Dictionary<IvyTokenKind, IClassificationType>();
      _typeMap[IvyTokenKind.Keyword] = standards.Keyword;
      _typeMap[IvyTokenKind.BuiltInType] = standards.Keyword;
      _typeMap[IvyTokenKind.Number] = standards.NumberLiteral;
      _typeMap[IvyTokenKind.String] = standards.StringLiteral;
      _typeMap[IvyTokenKind.Comment] = standards.Comment;
      _typeMap[IvyTokenKind.VariableIdentifier] = standards.Identifier;

    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    public IEnumerable<ITagSpan<ClassificationTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      var snapshot = spans[0].Snapshot;
      foreach (var tagSpan in this._aggregator.GetTags(spans)) {
        IClassificationType t = _typeMap[tagSpan.Tag.Kind];
        foreach (SnapshotSpan s in tagSpan.Span.GetSpans(snapshot)) {
          yield return new TagSpan<ClassificationTag>(s, new ClassificationTag(t));
        }
      }
    }

    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
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

  /// <summary>
  /// Defines an editor format for user-defined type.
  /// </summary>
  [Export(typeof(EditorFormatDefinition))]
  [ClassificationType(ClassificationTypeNames = "Ivy identifier")]
  [Name("Ivy identifier")]
  [UserVisible(true)]
  //set the priority to be after the default classifiers
  [Order(Before = Priority.Default)]
  internal sealed class IvyTypeFormat : ClassificationFormatDefinition
  {
    public IvyTypeFormat() {
      this.DisplayName = "Ivy identifier"; //human readable version of the name
      this.ForegroundColor = Colors.CornflowerBlue;
    }
  }

  internal static class ClassificationDefinition
  {
    /// <summary>
    /// Defines the "ordinary" classification type.
    /// </summary>
    [Export(typeof(ClassificationTypeDefinition))]
    [Name("Ivy identifier")]
    internal static ClassificationTypeDefinition UserType = null;
  }



  #endregion

}
