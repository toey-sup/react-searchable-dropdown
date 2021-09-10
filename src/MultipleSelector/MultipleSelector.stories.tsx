import { Meta } from "@storybook/react/types-6-0";
import { Story } from "@storybook/react";
import MultipleSelector, { Props } from "./MultipleSelector";

export default {
  title: "Components/MultipleSelector",
  component: MultipleSelector,
  argTypes: {
    backgroundColor: { control: 'color' },
  },
  args: {
    label: 'Mul-Selector',
    popUpKey: 'Mul-Selector-key',
    choiceSections: [{ sectionName: 'Single Choice', choices: [{ label: 'Special One', singleChoice: true }]}, { choices: [{ label: 'A' }, { label: 'B' }, { label: 'A' }, { label: 'C' }, { label: 'D' }, { label: 'E' }, { label: 'F' }, { label: 'G' }, { label: 'H' }, { label: 'I' }, { label: 'J' }, { label: 'K' }, { label: 'L' }, { label: 'M' }, { label: 'N' }] }],
    name: 'Mul-Selector-name',
    placeholder: 'please select choices',
    id: 'Mul-Selector-id',
    handleSelect: ({ value, name }) => { console.log({ value, name })},
  }
} as Meta<Props>;

// Create a master template for mapping args to render the Button component
const Template: Story<Props> = (args) => <MultipleSelector {...args} />;

// Reuse that template for creating different stories
export const Normal = Template.bind({});
