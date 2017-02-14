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
		public static List<OclComparison> comparisonList;

		UmlMethodNode selectedMethod;
		OclCondition selectedCondition;
		OclCondition selectedPrecondition;
		OclCondition selectedPostcondition;

		public MainWindow()
		{
			InitializeComponent();

			umlFile = new XmlDocument();
			string comparisons = File.ReadAllText(@"../../../util/comparisons.json");
			List<dynamic> items = JsonConvert.DeserializeObject<List<dynamic>>(comparisons);

			comparisonList = new List<OclComparison>();

			foreach (dynamic b in items)
			{
				string name = b.name;
				string symbol = b.symbol;
				string smtSymbol = null;
				bool? invertable = null;

				try { smtSymbol = b.smtSymbol; }
				catch (Exception ex) { }

				try { invertable = b.invertable; }
				catch (Exception ex) { }

				comparisonList.Add(new OclComparison(name, symbol, smtSymbol, invertable));
			}

			// TODO: This should change depending on the current types being compared.
			comboBoxComparator.ItemsSource = comparisonList;
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

			this.comboBoxMethod.ItemsSource = node.Methods.Keys;

			this.listBoxPreconditions.Items.Refresh();
			this.listBoxPreconditions.ItemsSource = null;
			this.comboBoxComparator.SelectedIndex = -1;
			this.textBoxArgumentLeft.Text = "";
			this.textBoxArgumentRight.Text = "";
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

				this.listBoxPreconditions.ItemsSource = this.selectedMethod.Preconditions;
				this.listBoxPreconditions.Items.Refresh();
				this.listBoxPostconditions.ItemsSource = this.selectedMethod.Postconditions;
				this.listBoxPostconditions.Items.Refresh();
				this.listBoxLinkedPreconditions.ItemsSource = this.selectedMethod.Preconditions;
				this.listBoxLinkedPreconditions.Items.Refresh();
			}
		}

		private void buttonAddPrecondition_Click(object sender, RoutedEventArgs e)
		{
			selectedMethod.AddCondition("pre");
			this.listBoxPreconditions.Items.Refresh();
		}

		private void buttonRemovePrecondition_Click(object sender, RoutedEventArgs e)
		{
			int index = listBoxPreconditions.SelectedIndex;

			if (index >= 0)
			{
				selectedMethod.RemoveCondition("pre", index);
				this.listBoxPreconditions.Items.Refresh();
			}
		}

		private void buttonAddPostcondition_Click(object sender, RoutedEventArgs e)
		{
			selectedMethod.AddCondition("post");
			this.listBoxPreconditions.Items.Refresh();
		}

		private void buttonRemovePostcondition_Click(object sender, RoutedEventArgs e)
		{
			int index = listBoxPostconditions.SelectedIndex;

			if (index >= 0)
			{
				selectedMethod.RemoveCondition("post", index);
				this.listBoxPreconditions.Items.Refresh();
			}
		}

		private void listBoxPreconditions_GotFocus(object sender, RoutedEventArgs e)
		{
			if (listBoxPreconditions.SelectedIndex >= 0)
			{
				UpdateSelectedPrecondition();
			}
		}

		private void listBoxPreconditions_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			UpdateSelectedPrecondition();
		}

		private void UpdateSelectedPrecondition()
		{
			if (listBoxPreconditions.SelectedIndex >= 0)
			{
				selectedPrecondition = listBoxPreconditions.SelectedItem as OclCondition;
				selectedCondition = selectedPrecondition;
				UpdateConditionControls();
				this.listBoxLinkedPreconditions.IsEnabled = false;
				this.listBoxLinkedPreconditions.UnselectAll();
			}
			else
			{
				comboBoxComparator.SelectedIndex = -1;
				textBoxArgumentLeft.Text = "";
				textBoxArgumentRight.Text = "";
				checkBoxInvertCondition.IsChecked = false;
				textBoxExceptionCondition.Text = "";
			}
		}

		private void listBoxPostconditions_GotFocus(object sender, RoutedEventArgs e)
		{
			if (listBoxPostconditions.SelectedIndex >= 0 &&
				selectedCondition != selectedPostcondition)
			{
				UpdateSelectedPostcondition();
			}
		}

		private void listBoxPostconditions_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			UpdateSelectedPostcondition();
		}

		private void UpdateSelectedPostcondition()
		{
			if (listBoxPostconditions.SelectedIndex >= 0)
			{
				selectedPostcondition = listBoxPostconditions.SelectedItem as LinkedOclCondition;
				selectedCondition = null;
				this.listBoxLinkedPreconditions.UnselectAll();
				selectedCondition = selectedPostcondition;
				UpdateConditionControls();
				this.listBoxLinkedPreconditions.IsEnabled = true;
				List<OclCondition> linkedConditions = (selectedCondition as LinkedOclCondition).LinkedConditions;
				foreach (OclCondition c in linkedConditions)
				{
					this.listBoxLinkedPreconditions.SelectedItems.Add(c);
				}
			}
			else
			{
				comboBoxComparator.SelectedIndex = -1;
				textBoxArgumentLeft.Text = "";
				textBoxArgumentRight.Text = "";
				checkBoxInvertCondition.IsChecked = false;
				textBoxExceptionCondition.Text = "";
			}
		}

		private void UpdateConditionControls()
		{
			// Comparator combo box
			if (selectedCondition.Comparator != null)
			{
				comboBoxComparator.SelectedItem = selectedCondition.Comparator;
			}
			else
			{
				comboBoxComparator.SelectedIndex = -1;
			}

			// Argument text boxes
			textBoxArgumentLeft.Text = selectedCondition.GetArgument(0);
			textBoxArgumentRight.Text = selectedCondition.GetArgument(1);

			// Inverted checkbox
			checkBoxInvertCondition.IsChecked = selectedCondition.IsInverted;

			// Exception text box
			textBoxExceptionCondition.Text = selectedCondition.Exception;
		}

		private void comboBoxComparator_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			if (comboBoxComparator.SelectedItem != null)
			{
				OclComparison item = comboBoxComparator.SelectedItem as OclComparison;
				selectedCondition.Comparator = item;
				this.listBoxPreconditions.Items.Refresh();
				this.listBoxPostconditions.Items.Refresh();
			}
		}

		private void textBoxArgumentLeft_TextChanged(object sender, TextChangedEventArgs e)
		{
			selectedCondition.SetArgument(0, textBoxArgumentLeft.Text);
			this.listBoxPreconditions.Items.Refresh();
			this.listBoxPostconditions.Items.Refresh();
		}

		private void textBoxArgumentRight_TextChanged(object sender, TextChangedEventArgs e)
		{
			selectedCondition.SetArgument(1, textBoxArgumentRight.Text);
			this.listBoxPreconditions.Items.Refresh();
			this.listBoxPostconditions.Items.Refresh();
		}

		private void textBoxExceptionCondition_TextChanged(object sender, TextChangedEventArgs e)
		{
			selectedCondition.SetException(textBoxExceptionCondition.Text);
			this.listBoxPreconditions.Items.Refresh();
			this.listBoxPostconditions.Items.Refresh();
		}

		private void checkBoxInvertCondition_CheckedChanged(object sender, RoutedEventArgs e)
		{
			if (selectedCondition.Comparator != null)
			{
				bool isChecked = checkBoxInvertCondition.IsChecked == true;
				selectedCondition.SetInverted(isChecked);

				this.listBoxPreconditions.Items.Refresh();
				this.listBoxPostconditions.Items.Refresh();
			}
		}

		private void listBoxLinkedPreconditions_SelectionChanged(object sender, SelectionChangedEventArgs e)
		{
			if (selectedCondition == selectedPostcondition)
			{
				List<OclCondition> conditions = listBoxLinkedPreconditions.SelectedItems.Cast<OclCondition>().ToList();
				LinkedOclCondition condition = selectedPostcondition as LinkedOclCondition;
				condition.LinkedConditions = conditions;
				this.listBoxPreconditions.Items.Refresh();
				this.listBoxPostconditions.Items.Refresh();
			}
		}
	}
}
