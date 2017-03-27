using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Linq;
using Microsoft.VisualStudio.Language.Intellisense;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;


namespace IvyLanguage
{

  #region Source Provider

  [Export(typeof(IQuickInfoSourceProvider))]
  [ContentType("ivy")]
  [Name("Ivy QuickInfo")]
  class IvyQuickInfoSourceProvider : IQuickInfoSourceProvider
  {
    [Import]
    IBufferTagAggregatorFactoryService aggService = null;

    public IQuickInfoSource TryCreateQuickInfoSource(ITextBuffer textBuffer) {
      return new IvyQuickInfoSource(textBuffer, aggService.CreateTagAggregator<IvyTokenTag>(textBuffer));
    }
  }

  class IvyQuickInfoSource : IQuickInfoSource
  {
    private ITagAggregator<IvyTokenTag> _aggregator;
    private ITextBuffer _buffer;

    public IvyQuickInfoSource(ITextBuffer buffer, ITagAggregator<IvyTokenTag> aggregator)
    {
      _aggregator = aggregator;
      _buffer = buffer;
    }

    public void AugmentQuickInfoSession(IQuickInfoSession session, IList<object> quickInfoContent, out ITrackingSpan applicableToSpan)
    {
      applicableToSpan = null;

      var triggerPoint = (SnapshotPoint)session.GetTriggerPoint(_buffer.CurrentSnapshot);
      if (triggerPoint == null)
        return;

      foreach (IMappingTagSpan<IvyTokenTag> curTag in _aggregator.GetTags(new SnapshotSpan(triggerPoint, triggerPoint)))
      {
        var s = curTag.Tag.HoverText;
        if (s != null)
        {
          var tagSpan = curTag.Span.GetSpans(_buffer).First();
          applicableToSpan = _buffer.CurrentSnapshot.CreateTrackingSpan(tagSpan, SpanTrackingMode.EdgeExclusive);
          quickInfoContent.Add(s);
        }
      }
    }
    public void Dispose()
    {
    }
  }

  #endregion


  #region Controller Provider

  [Export(typeof(IIntellisenseControllerProvider))]
  [Name("Ivy QuickInfo controller")]
  [ContentType("ivy")]
  class IvyQuickInfoControllerProvider : IIntellisenseControllerProvider
  {
    [Import]
    internal IQuickInfoBroker QuickInfoBroker { get; set; }

    public IIntellisenseController TryCreateIntellisenseController(ITextView textView, IList<ITextBuffer> subjectBuffers) {
      return new IvyQuickInfoController(textView, subjectBuffers, this);
    }
  }

  #endregion


  #region Controller

  class IvyQuickInfoController : IIntellisenseController
  {
    private ITextView _textView;
    private IList<ITextBuffer> _subjectBuffers;
    private IvyQuickInfoControllerProvider _componentContext;

    private IQuickInfoSession _session;

    internal IvyQuickInfoController(ITextView textView, IList<ITextBuffer> subjectBuffers, IvyQuickInfoControllerProvider componentContext) {
      _textView = textView;
      _subjectBuffers = subjectBuffers;
      _componentContext = componentContext;

      _textView.MouseHover += this.OnTextViewMouseHover;
    }

    public void ConnectSubjectBuffer(ITextBuffer subjectBuffer) {
    }

    public void DisconnectSubjectBuffer(ITextBuffer subjectBuffer) {
    }

    public void Detach(ITextView textView) {
      if (_textView == textView) {
        _textView.MouseHover -= OnTextViewMouseHover;
        _textView = null;
      }
    }

    void OnTextViewMouseHover(object sender, MouseHoverEventArgs e) {
      SnapshotPoint? point = GetMousePosition(new SnapshotPoint(_textView.TextSnapshot, e.Position));

      if (point != null) {
        ITrackingPoint triggerPoint = point.Value.Snapshot.CreateTrackingPoint(point.Value.Position, PointTrackingMode.Positive);

        // Find the broker for this buffer
        if (!_componentContext.QuickInfoBroker.IsQuickInfoActive(_textView)) {
          _session = _componentContext.QuickInfoBroker.CreateQuickInfoSession(_textView, triggerPoint, true);
          _session.Start();
        }
      }
    }

    SnapshotPoint? GetMousePosition(SnapshotPoint topPosition) {
      return _textView.BufferGraph.MapDownToFirstMatch(
        topPosition,
        PointTrackingMode.Positive,
        snapshot => _subjectBuffers.Contains(snapshot.TextBuffer),
        PositionAffinity.Predecessor);
    }
  }

  #endregion

}
