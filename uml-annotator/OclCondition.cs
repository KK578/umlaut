using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	public class OclCondition
	{
		public OclComparison Comparator { get; set; }
		private List<string> arguments;

		public OclCondition()
		{
			arguments = new List<string>();
		}

		public OclCondition(string condition)
		{
			string innerCondition = condition;
			if (innerCondition.StartsWith("("))
			{
				innerCondition = innerCondition.Substring(1, innerCondition.Length - 2);
			}

			string[] items = innerCondition.Split(' ');
			Comparator = FindComparison(items[0]);

			arguments = new List<string>();
			for (int i = 1; i < items.Length; i++)
			{
				arguments.Add(items[i]);
			}
		}

		public void SetArguments(string argument)
		{
			arguments = new List<string>(Regex.Split(argument, "\r?\n"));
		}

		public string GetArgumentsString()
		{
			return String.Join("\r\n", arguments);
		}

		private OclComparison FindComparison(string comparison)
		{
			// HACK: See MainWindow for explanation.
			List<OclComparison> comparisons = MainWindow.comparisonLists["numeric"];

			foreach (OclComparison c in comparisons)
			{
				if (comparison == c.SymbolString())
				{
					return c;
				}
			}

			return null;
		}

		public override string ToString()
		{
			string comparison = "";

			if (Comparator != null)
			{
				comparison = Comparator.SymbolString();
			}

			return String.Format("({0} {1})", comparison, String.Join(" ", arguments));
		}
	}
}
