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
		Dictionary<string, UmlClassNode> classes;

		public MainWindow()
		{
			InitializeComponent();

			umlFile = new XmlDocument();
		}

		private void UmlFindClasses()
		{
			classes = new Dictionary<string, UmlClassNode>();

			if (umlFile.HasChildNodes)
			{
				XmlNodeList list = umlFile.GetElementsByTagName("class");

				for (int i = 0; i < list.Count; i++)
				{
					// Store related node based on class name.
					XmlNode node = list[i];
					string name = node.Attributes.GetNamedItem("name").Value;

					classes.Add(name, new UmlClassNode(node));
				}
			}

			comboBoxClass.ItemsSource = classes.Keys;
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

		private void buttonSave_Click(object sender, RoutedEventArgs e)
		{
			SaveFileDialog dialog = new SaveFileDialog();

			if (dialog.ShowDialog() == true)
			{
				XmlWriterSettings settings = new XmlWriterSettings();
				settings.Indent = true;

				using (XmlWriter writer = XmlWriter.Create(dialog.FileName, settings))
				{
					umlFile.WriteTo(writer);
				}
			}
		}

		private void comboBoxClass_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			string selectedClass = comboBoxClass.SelectedValue.ToString();
			UmlClassNode node = classes[selectedClass];

			comboBoxMethod.ItemsSource = node.Methods.Keys;
		}

		private void comboBoxMethod_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			string selectedClass = comboBoxClass.SelectedValue.ToString();
			string selectedMethod = comboBoxMethod.SelectedValue.ToString();
			UmlClassNode classNode = classes[selectedClass];
			UmlMethodNode methodNode = classNode.Methods[selectedMethod];
		}

		private class UmlClassNode
		{
			XmlNode umlClass;
			private Dictionary<string, UmlMethodNode> methods;
			private Dictionary<string, XmlNode> variables;

			// TODO: Hacky exposing dictionary directly.
			// Should only allow access to Keys or the Values.
			public Dictionary<string, UmlMethodNode> Methods
			{
				get { return methods; }
			}
			public Dictionary<string, XmlNode> Variables
			{
				get { return variables; }
			}

			public UmlClassNode(XmlNode umlClass)
			{
				this.umlClass = umlClass;

				ParseClass();
			}

			private void ParseClass()
			{
				XmlNodeList children = umlClass.ChildNodes;

				foreach (XmlNode child in children) {
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
			private Dictionary<string, XmlNode> argumentNodes;
			private XmlNode returnNode;

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
								preconditionNode = node.FirstChild.Attributes.GetNamedItem("value");
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
								postconditionNode = node.FirstChild.Attributes.GetNamedItem("value");
								break;
							}
						}
					}
				}

				XmlDocument doc = node.OwnerDocument;

				// Create nodes in place if they don't already exist.
				if (preconditionNode == null)
				{
					preconditionNode = doc.CreateElement("preconditionsInternal");
					node.AppendChild(preconditionNode);

					preconditionNode = PopulateConstraintNode(preconditionNode);
				}

				if (postconditionNode == null)
				{
					postconditionNode = doc.CreateElement("postconditionsInternal");
					node.AppendChild(postconditionNode);

					postconditionNode = PopulateConstraintNode(postconditionNode);
				}
			}

			private XmlNode PopulateConstraintNode(XmlNode node)
			{
				XmlDocument doc = node.OwnerDocument;
				XmlNode constraintNode = doc.CreateElement("constraint");
				XmlNode specificationNode = doc.CreateElement("specification");
				XmlNode literalStringNode = doc.CreateElement("literalString");
				XmlNode valueNode = doc.CreateAttribute("value");
				valueNode.InnerText = "";
				literalStringNode.Attributes.SetNamedItem(valueNode);
				specificationNode.AppendChild(literalStringNode);
				constraintNode.AppendChild(specificationNode);
				node.AppendChild(constraintNode);

				return valueNode;
			}

			private void ParseArguments(XmlNodeList arguments)
			{
				argumentNodes = new Dictionary<string, XmlNode>();

				foreach (XmlNode child in arguments)
				{
					XmlNode argument = child.ChildNodes[0];
					string direction = argument.Attributes.GetNamedItem("direction").Value;

					if (direction == "In")
					{
						string name = argument.Attributes.GetNamedItem("name").Value;
						argumentNodes.Add(name, argument);
					}
					else if (direction == "Return")
					{
						returnNode = argument;
					}
				}
			}
		}
	}
}
