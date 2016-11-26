using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Data;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Windows.Navigation;
using System.Windows.Shapes;
using System.Xml;

using Microsoft.Win32;

namespace UmlAnnotator
{
	/// <summary>
	/// Interaction logic for MainWindow.xaml
	/// </summary>
	public partial class MainWindow : Window
	{
		XmlDocument umlFile;
		Dictionary<string, XmlNode> classes;

		public MainWindow()
		{
			InitializeComponent();

			umlFile = new XmlDocument();
		}

		private void UmlFindClasses()
		{
			classes = new Dictionary<string, XmlNode>();

			if (umlFile.HasChildNodes)
			{
				XmlNodeList list = umlFile.GetElementsByTagName("class");

				for (int i = 0; i < list.Count; i++)
				{
					// Store related node based on class name.
					XmlNode node = list[i];
					string name = node.Attributes.GetNamedItem("name").InnerText;

					classes.Add(name, node);
				}
			}

			comboBox.ItemsSource = classes.Keys;
		}

		private void buttonLoad_Click(object sender, RoutedEventArgs e)
		{
			OpenFileDialog dialog = new OpenFileDialog();

			if (dialog.ShowDialog() == true)
			{
				try
				{
					umlFile.Load(dialog.FileName);
				}
				catch
				{
					MessageBox.Show("Invalid XML File.");
					return;
				}

				// TODO: Make it observer based?
				UmlFindClasses();
			}
		}
	}
}
