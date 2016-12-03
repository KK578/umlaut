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

using Newtonsoft.Json;

using Microsoft.Win32;
using System.IO;

namespace UmlAnnotator
{
	/// <summary>
	/// Interaction logic for MainWindow.xaml
	/// </summary>
	public partial class MainWindow : Window
	{
		XmlDocument umlFile;
		Dictionary<string, UmlClassNode> classes;

		// HACK: Exposed due to use at OclCondition.
		// Passing through files would involve passing the list through:
		//  UmlClassNode -> UmlMethodNode -> OclCondition
		// Would still like this to be neater somehow.
		public static Dictionary<string, List<OclComparison>> comparisonLists;

		UmlMethodNode selectedMethod;
		OclCondition selectedCondition;

		public MainWindow()
		{
			InitializeComponent();

			umlFile = new XmlDocument();
			string comparisons = File.ReadAllText(@"../../../util/comparisons.json");
			Dictionary<string, List<dynamic>> items = JsonConvert.DeserializeObject<Dictionary<string, List<dynamic>>>(comparisons);

			comparisonLists = new Dictionary<string, List<OclComparison>>();

			foreach (KeyValuePair<string, List<dynamic>> a in items)
			{
				List<OclComparison> list = new List<OclComparison>();

				foreach (dynamic b in a.Value)
				{
					string name = b.name;
					string symbol = b.symbol;
					string smtSymbol = null;
					bool? invertable = null;

					try { smtSymbol = b.smtSymbol; }
					catch (Exception ex) { }

					try { invertable = b.invertable; }
					catch (Exception ex) { }

					list.Add(new OclComparison(name, symbol, smtSymbol, invertable));
				}

				comparisonLists.Add(a.Key, list);
			}

			// TODO: This should change depending on the current types being compared.
			comboBoxComparator.ItemsSource = comparisonLists["numeric"];
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
			// Save data to nodes before save
			foreach (UmlClassNode node in classes.Values)
			{
				node.UpdateNodes();
			}

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

			radioButtonPreconditions.IsChecked = false;
			radioButtonPostconditions.IsChecked = false;

			listBoxConditions.ItemsSource = null;
			listBoxConditions.Items.Refresh();
			comboBoxComparator.SelectedIndex = -1;
			textBoxArguments.Text = "";
		}

		private void comboBoxMethod_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			if (comboBoxClass.SelectedIndex >= 0 && comboBoxMethod.SelectedIndex >= 0)
			{
				string selectedClass = comboBoxClass.SelectedValue.ToString();
				string selectedMethod = comboBoxMethod.SelectedValue.ToString();
				UmlClassNode classNode = classes[selectedClass];
				UmlMethodNode methodNode = classNode.Methods[selectedMethod];

				this.selectedMethod = methodNode;

				if (radioButtonPreconditions.IsChecked == true)
				{
					this.listBoxConditions.ItemsSource = this.selectedMethod.Preconditions;
				}
				else if (radioButtonPostconditions.IsChecked == true)
				{
					this.listBoxConditions.ItemsSource = this.selectedMethod.Postconditions;
				}

				listBoxConditions.Items.Refresh();
			}
		}

		private void radioButtonPreconditions_Checked(object sender, RoutedEventArgs e)
		{
			this.listBoxConditions.ItemsSource = this.selectedMethod.Preconditions;
			listBoxConditions.Items.Refresh();
		}

		private void radioButtonPostconditions_Checked(object sender, RoutedEventArgs e)
		{
			this.listBoxConditions.ItemsSource = this.selectedMethod.Postconditions;
			listBoxConditions.Items.Refresh();
		}

		private void buttonAddCondition_Click(object sender, RoutedEventArgs e)
		{
			if (radioButtonPreconditions.IsChecked == true)
			{
				selectedMethod.AddCondition("pre");
			}
			else if (radioButtonPostconditions.IsChecked == true)
			{
				selectedMethod.AddCondition("post");
			}

			listBoxConditions.Items.Refresh();
		}

		private void listBoxConditions_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			if (listBoxConditions.SelectedIndex >= 0)
			{
				selectedCondition = listBoxConditions.SelectedItem as OclCondition;

				if (selectedCondition.Comparator != null)
				{
					comboBoxComparator.SelectedItem = selectedCondition.Comparator;
				}
				else
				{
					comboBoxComparator.SelectedIndex = -1;
				}

				textBoxArguments.Text = selectedCondition.GetArgumentsString();
			}
			else
			{
				comboBoxComparator.SelectedIndex = -1;
				textBoxArguments.Text = "";
			}
		}

		private void comboBoxComparator_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			if (comboBoxComparator.SelectedItem != null)
			{
				OclComparison item = comboBoxComparator.SelectedItem as OclComparison;
				selectedCondition.Comparator = item;
				listBoxConditions.Items.Refresh();
			}
		}

		private void textBoxArguments_TextChanged(object sender, TextChangedEventArgs e)
		{
			if (!String.IsNullOrWhiteSpace(textBoxArguments.Text))
			{
				selectedCondition.SetArguments(textBoxArguments.Text);
				listBoxConditions.Items.Refresh();
			}
		}
	}
}
