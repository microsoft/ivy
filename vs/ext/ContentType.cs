using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Utilities;


namespace IvyLanguage
{
  class IvyContentType
  {
    [Export]
    [Name("ivy")]
    [BaseDefinition("code")]
    internal static ContentTypeDefinition ContentType = null;

    [Export(typeof(IWpfTextViewCreationListener))]
    [ContentType("text")]
    [TextViewRole(PredefinedTextViewRoles.Document)]
    internal sealed class IvyTextViewCreationListener : IWpfTextViewCreationListener
    {
      [Export(typeof(AdornmentLayerDefinition))]
      [Name("ModelAdornment")]
      [Order(After = PredefinedAdornmentLayers.Selection, Before = PredefinedAdornmentLayers.Text)]
      [TextViewRole(PredefinedTextViewRoles.Document)]
      public AdornmentLayerDefinition editorAdornmentLayer = null;
      public void TextViewCreated(IWpfTextView textView)
      {
      }
    }

    [Export]
    [FileExtension(".ivy")]
    [ContentType("ivy")]
    internal static FileExtensionToContentTypeDefinition FileType = null;
  }
}
