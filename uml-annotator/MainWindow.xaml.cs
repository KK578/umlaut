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
			Dictionary<string, UmlMethodNode> methods;
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
						ParseMethods(child.ChildNodes);
					}
					else if (child.Name == "ownedAttributesInternal")
					{
						ParseVariables(child.ChildNodes);
					}
				}

				PrintDebug();
			}

			private void ParseMethods(XmlNodeList methods)
			{
				this.methods = new Dictionary<string, UmlMethodNode>();

				foreach (XmlNode node in methods)
				{
					UmlMethodNode method = new UmlMethodNode(node);
					string methodName = method.Name;

					this.methods.Add(methodName, method);
				}
			}

			private void ParseVariables(XmlNodeList variables)
			{
				this.variables = new Dictionary<string, XmlNode>();

				foreach (XmlNode variable in variables)
				{
					string variableName = variable.Attributes.GetNamedItem("name").Value;
					this.variables.Add(variableName, variable);
				}
			}

			private void PrintDebug()
			{
				foreach (KeyValuePair<string, XmlNode> a in variables)
				{
					Console.WriteLine("Variable: " + a.Key);
				}

				foreach (KeyValuePair<string, UmlMethodNode> a in methods)
				{
					Console.WriteLine("Method: " + a.Key);
				}
			}
		}

		private class UmlMethodNode
		{
			private string name;
			public string Name
			{
				get { return name; }
			}

			private XmlNode node;
			private XmlNode preconditionNode;
			private XmlNode postconditionNode;

			public UmlMethodNode(XmlNode node)
			{
				this.node = node;
				this.name = node.Attributes.GetNamedItem("name").Value;

				ParseMethod();
			}

			private void ParseMethod()
			{
				XmlNodeList children = node.ChildNodes;

				foreach (XmlNode child in children)
				{
					if (child.Name == "ownedParameters")
					{
						ParseArguments(child.ChildNodes);
					}
					else if (child.Name == "preconditionsInternal")
					{
						XmlNode constraintNode = child.FirstChild;
						foreach (XmlNode node in constraintNode.ChildNodes)
						{
							if (node.Name == "specification")
							{
								preconditionNode = node.FirstChild;
								break;
							}
						}
					}
					else if (child.Name == "postconditionsInternal")
					{
						XmlNode constraintNode = child.FirstChild;
						foreach (XmlNode node in constraintNode.ChildNodes)
						{
							if (node.Name == "specification")
							{
								postconditionNode = node.FirstChild;
								break;
							}
						}
					}
				}
			}

			private void ParseArguments(XmlNodeList arguments)
			{
				foreach (XmlNode child in arguments)
				{
					XmlNode argument = child.ChildNodes[0];
					string direction = argument.Attributes.GetNamedItem("direction").Value;

					if (direction == "In")
					{
						Console.WriteLine(argument.Attributes.GetNamedItem("name").Value);
					}
					else if (direction == "Return")
					{

					}
				}
			}
		}
	}
}
