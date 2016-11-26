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
					string name = node.Attributes.GetNamedItem("name").Value;

					classes.Add(name, node);

					UmlClassNode thing = new UmlClassNode(node);
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

		private void comboBox_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			string selectedClass = comboBox.SelectedValue.ToString();
			XmlNode node = classes[selectedClass];
			XmlNodeList nodeChildren = node.ChildNodes;

			for (int i = 0; i < nodeChildren.Count; i++)
			{
				XmlNode child = nodeChildren[i];

				if (child.Name == "ownedOperationsInternal")
				{
					XmlNodeList methodList = child.ChildNodes;

					for (int j = 0; j < methodList.Count; j++)
					{
						XmlNode method = methodList[j];

						Console.WriteLine(method.Attributes.GetNamedItem("name").Value);
					}
				}
			}
		}

		private class UmlClassNode
		{
			XmlNode umlClass;
			Dictionary<string, XmlNode> methods;
			Dictionary<string, XmlNode> variables;

			public UmlClassNode(XmlNode umlClass)
			{
				this.umlClass = umlClass;

				ParseClass();
			}

			private void ParseClass()
			{
				XmlNodeList children = umlClass.ChildNodes;

				for (int i = 0; i < children.Count; i++)
				{
					XmlNode child = children[i];

					if (child.Name == "ownedOperationsInternal")
					{
						methods = ParseChildNodes(child.ChildNodes);
					}
					else if (child.Name == "ownedAttributesInternal")
					{
						variables = ParseChildNodes(child.ChildNodes);
					}
				}

				PrintDebug();
			}

			private Dictionary<string, XmlNode> ParseChildNodes(XmlNodeList list)
			{
				Dictionary<string, XmlNode> dictionary = new Dictionary<string, XmlNode>();

				foreach (XmlNode item in list)
				{
					string name = item.Attributes.GetNamedItem("name").Value;
					dictionary.Add(name, item);
				}

				return dictionary;
			}

			private void PrintDebug()
			{
				foreach (KeyValuePair<string, XmlNode> a in variables)
				{
					Console.WriteLine("Variable: " + a.Key);
				}

				foreach (KeyValuePair<string, XmlNode> a in methods)
				{
					Console.WriteLine("Method: " + a.Key);
				}
			}
		}
	}
}
